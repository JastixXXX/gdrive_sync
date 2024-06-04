# This scrypt is for syncing a local directory with a directory on
# Google Drive. Takes three arguments: the local directory absolute path
# the google drive os-like path, i.e. a path relative to the
# Google Drive root <foldername>/<innerfolder>/...
# and a list of objects to not sync
# With flag -n --new a new gdrive directory will be created instead of
# searching an existing one
# Argument --sync-direction handles file deletions. It has three
# options: "gdrive_to_local", "local_to_gdrive", "mirror"

# The logic of syncing - go over either local or gdrive files.
# If anything is newer on a local machine - upload it to gdrive,
# if anything is newer on gdrive - download to a local machine.
# Always!
# But we have to deal with file removal as well
# So, basically we have two cases:
# 1. Something is deleted locally or added to gdrive - absent on
# local machine but exists on gdrive
# 2. Something was deleted from gdrive or added locally - it's on
# the local machine, but not on gdrive
# For the purpose to set, what to do with absent files "sync
# direction" parameter is used. By default it will be "to gdrive",
# so nothing will be deleted on a local machine.
# If it's set "to local", then nothing will be deleted from gdrive
# This is clear behavior, but there is a case: for example
# we forgot to sync FROM gdrive and begun to sync TO gdrive.
# If there were new files on gdrive, they will be removed,
# unlike existing on both drives files, which modification
# time will be compared and newer files downloaded regardles
# of the sync direction. To prevent it there is another option -
# "mirror". If it's set, there will be no
# deletions in the syncing process. Files, absent on the
# source will be downloaded, files, absent on the target
# will be uploaded.
# The best option to use the script - put syncing "mirror"
# on autolaunch, and both "local_to_gdrive" and "gdrive_to_local"
# at button press. So if during a day there were some deletions,
# just press a button.

import logging
import subprocess
from os import path, listdir, remove, mkdir, utime
from os import name as os_name
from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google.auth.exceptions import TransportError, RefreshError
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from googleapiclient.http import MediaFileUpload, MediaIoBaseDownload
from io import FileIO, BytesIO
from httplib2 import ServerNotFoundError
from datetime import datetime, UTC
from concurrent.futures import TimeoutError
from time import sleep, time
from argparse import ArgumentParser, ArgumentTypeError
from typing import Literal
from shutil import rmtree
from datetime import datetime

# ================= globals ==================
GOOGLE_LOGIN = {
    # The CLIENT_SECRETS_FILE variable specifies the name of a file that contains
    # the OAuth 2.0 information for this application, including its client_id and
    # client_secret. Received from google cloud console
    'client_secrets_file': 'client_secret.json',
    # doesn't exist at the beginning, granted after user interaction
    'token_file': 'token.json',
    # If modifying these scopes, delete the file token.json.
    'scopes': ['https://www.googleapis.com/auth/drive']
}
# =============== end globals ================

class IgnoreThose:
    """this class is for storing paths to files or folders to ignore.
    Type of ignored objects can be specified: 'single_file',
    'all_files' but not folders in a given folder, whole 'folder'.
    """
    def __init__(
        self,
        rel_path: str,
        obj_type: Literal['single_file', 'all_files', 'folder']
    ) -> None:
        # exclude a situation when the whole syncing folder is excluded
        # it's a pure usage mistake
        if not rel_path and obj_type == 'folder':
            raise ValueError('"rel_path" for ignoring is pointing to the root folder, nothing to sync')
        # preserve the ignored object type
        self.obj_type = obj_type
        # strip slashes
        if os_name == 'posix':
            rel_path = rel_path.strip('/')
        else:
            rel_path = rel_path.strip('\\')
        # preserve the whole rel_path
        self.rel_path = rel_path
        # for a single file or a folder the given path contains
        # both - obj name and obj relative path
        # we aren't preserving memory, so let's prepare all the
        # parts may be required
        if obj_type == 'all_files':
            # there isn't some object, we ignoring all files
            self.obj_name = None
            self.parents = rel_path
        else:
            # extract the last item from the path, it's the
            # object name and it' path
            self.obj_name = path.basename(rel_path)
            self.parents = path.dirname(rel_path)
        # tier to ease the search
        self.tier = len(self.parents)
        
class OneLocalTier:
    """this class is meant to store lists of filenames and
    directory names in some direcorty and parents as a relative path
    for a local folder
    """
    def __init__(self, parents: str='') -> None:
        """files and dirs are initialized as empty lists, so
        elements can be added there in a loop. tier is the amount
        of parents, i.e. the amount of directories in relative path

        Args:
            parents (str, optional): relative path to a file or directory
                        in the set root directory
        """
        self.files = []
        self.dirs = []
        self.parents = parents
        # strip all slashes except those which is inside a path
        # get tier lvl (tier 0, tier 1) counting it's parents
        if parents == '':
            self.tier = 0
        elif os_name == 'nt':
            self.tier = len(parents.strip('\\').split('\\'))
        else:
            self.tier = len(parents.strip('/').split('/'))

class OneGDriveTier(OneLocalTier):
    """this class is meant to store lists of filenames and
    directory names in some direcorty and parents on gdrive
    """
    def __init__(self, parents: str='', gparent: str='', synced: bool = False) -> None:
        """
        Takes two more parameters:

        "gparent" for gdrive items only, because they have relative path which is
        for a user and parent folder id, which is for API requests
        "synced" the idea is to go over local directories and sync all it's
        content with gdrive, marking such folders as synced. All remaining
        directories have to be copied to the local machine

        Args:
            gparent (str|None, optional): tier parent folder id
        """
        super().__init__(parents)
        self.gparent = gparent

class GdriveSync:
    def __init__(
        self,
        client_secrets_file: str,
        token_file: str,
        scopes: list[str],
        local_folder:str,
        gdrive_folder: str='',
        create_folder: bool=False,
        sync_direction: Literal['local_to_gdrive', 'gdrive_to_local', 'mirror']='local_to_gdrive',
        ignored_objects: list[IgnoreThose]|None = None
    ) -> None:
        self.client_secrets_file = client_secrets_file
        self.token_file = token_file
        self.scopes = scopes
        # folder name gdrive given by it's human readable path
        self.gdrive_folder = gdrive_folder.strip('/')
        # gdrive folder id, after it will be found or created
        self.gdrive_folder_id = None
        # a local folder to sync
        self.local_folder = local_folder
        # a flag to create a new folder
        self.create_folder = create_folder
        self.creds = None
        self.service = None
        # prepare for gdrive folder structure
        self.gdrive_struct = []
        # prepare for local structure
        self.local_struct = []
        # store stuff to ignore
        self.ignored_objects = ignored_objects
        self.sync_direction = sync_direction
        # when mirror is set, the whole dir should be restored
        self.restore_dirs = []

    def make_creds(self) -> None:
        """Takes care of OAuth2 authentification. Checks the token
        existence and it's validity, because the autch token expires
        in one hour. If necessary, user is asked to allow access
        to his account

        Raises:
            TransportError: any error, related with networking, signals
            about networking issues.
        """
        # The file token.json stores the user's access and refresh tokens, and is
        # created automatically when the authorization flow completes for the first
        # time.
        if path.exists(self.token_file):
            self.creds = Credentials.from_authorized_user_file(self.token_file)
        # If there are no (valid) credentials available, let the user log in.
        # Hopefully it's a one time action
        if self.creds is None or not self.creds.valid:
            self.service = None
            if self.creds and self.creds.expired and self.creds.refresh_token:
                try:
                    self.creds.refresh(Request())
                # if any error occured during requesting new access token
                # according to docs it will be this type
                except TransportError:
                    raise TransportError
            else:
                flow = InstalledAppFlow.from_client_secrets_file(self.client_secrets_file, self.scopes)
                try:
                    self.creds = flow.run_local_server(port=0, timeout_seconds=60)
                # if connection wasn't established, then when timeout is reached, we'll get
                # authorization_response = wsgi_app.last_request_uri.replace("http", "https")
                # AttributeError: 'NoneType' object has no attribute 'replace'
                except AttributeError:
                    # it's not a mistake. AttributeError doesn't explain what happened
                    # for a caller, but happens if no network
                    raise TransportError
            # Save the credentials for the next run
            with open(self.token_file, 'w') as token:
                token.write(self.creds.to_json())
        # make service
        if self.service is None:
            self.service = build('drive', 'v3', credentials=self.creds)
    
    def _get_folder_parent(self, item_id: str) -> str:
        """requests an id if a parent folder to item 'item_id'. Item can
        be either a file or a folder.

        Args:
            item_id (str): an id of an item, which parent we want to know

        Returns:
            str: an id of the item't parent
        """
        logger.debug(f'Getting folder parent of {item_id}')
        self.make_creds()
        directory = self.service.files().get(fileId=item_id, fields='parents').execute().get('parents', [])
        # returns an array, and parent always exists, unless we ask for
        # a parent of the root directory. But I didn't see it returnin
        # an array of more than one element
        return directory[0]

    def _search_sync_dir(self) -> tuple:
        """searches a directory on gdrive by a given path, if doesn't
        find it, creates a new one. Returns the directory id in any case

        Returns:
            tuple: a tuple, consists of two values - boolean, which is set
                        to True if the directory was found on gdrive and
                        False if created, and str - the directory id
        """
        logger.info(f'Searching sync directory {self.gdrive_folder} on gdrive')
        self.make_creds() # always check
        dir_exists = True # init with assumption we'll find the dir
        # gdrive doesn't support os-like paths, so we have to check
        # the existence of every item in the path chain
        folder_chain = self.gdrive_folder.split('/')
        parent_folder_id = 'root' # search start point
        while folder_chain:
            folder_name = folder_chain.pop(0) # get the topmost element
            # query to request a folder with required name and parent
            results = self.search_by_name(name=folder_name, parent_folder_id=parent_folder_id, obj_type='folder')
            # query = f"'{parent_folder_id}' in parents and name='{folder_name}' and trashed=false and mimeType = 'application/vnd.google-apps.folder'"
            # results = self.service.files().list(q=query, fields='files(id)').execute().get('files', [])
            # if found, then we can go deeper by the chain
            if results:
                # there can be two folders with the same name
                # but hopefully it's not our situation
                # otherwise it's not distinguisheable
                # taking the first one
                parent_folder_id = results[0]
            # if not found, then create the rest of the absent chain
            else:
                dir_exists = False
                # put back the removed above item, since we didn't find it
                folder_chain.insert(0, folder_name)
                # simply create all absent
                for item in folder_chain:
                    parent_folder_id = self.create_gdrive_folder(item, parent_folder_id)
                break
        logger.info(f'Found sync directory {self.gdrive_folder} on gdrive')
        return (dir_exists, parent_folder_id)

    def _iterate_gdrive(self, folder_id: str) -> None:
        """Takes folder_id as a starting point and gathers the
        gdrive structure to self.gdrive_struct, consisting of
        OneGDriveTier objects

        Args:
            folder_id (str): id of the folder on gdrive to make
                        the structure of
        """
        logger.debug('Start creating gdrive structure')
        self.make_creds() # always check
        parent_folder_id = folder_id # starting point
        parent_name = '' # relative root for os-like path
        dirs_to_visit = [] # nested dirs
        def one_tier_files() -> None:
            """Processes one folder, creating the OneGDriveTier object.
            Doesn't take or return anything because operates with
            it's parent function variables
            """
            for_return = OneGDriveTier(parents=parent_name, gparent=parent_folder_id) # init new
            # request the information about all contents of the folder
            current_dir = self.service.files().list(
                q=f"'{parent_folder_id}' in parents and trashed=false", fields="files(id, name, mimeType, modifiedTime)", pageSize=1000
            ).execute().get('files', [])
            for item in current_dir:
                # if folder, then preserve it's name and id in for result and
                # add to the list of nested folders - dirs_to_visit
                # so it's contents can be processed in the future as well
                if item['mimeType'] == 'application/vnd.google-apps.folder':
                    for_return.dirs.append((item['name'], item['id']))
                    dirs_to_visit.append((item['name'], item['id'], parent_name))
                    continue
                # if a file, then preserve it's name, id and modification time, converted to timestamp
                # but cut off numbers after dot via int
                else:
                    for_return.files.append((item['name'], item['id'], int(datetime.fromisoformat(item['modifiedTime']).timestamp())))
            self.gdrive_struct.append(for_return) # add new OneGDriveTier to the result
        # call for the root dir
        one_tier_files()
        # loop over all other dirs with any nesting inside the root dir
        while dirs_to_visit:
            dir_name, parent_folder_id, tmp_parent = dirs_to_visit.pop(0)
            parent_name = path.join(tmp_parent, dir_name)
            one_tier_files()
        logger.debug('Finished creating gdrive structure')

    def _iterate_localdir(self) -> None:
        """returns OneLocalTier object for each directory in a tree.
        For files - adds up a file modification type in a tuple
        (filename, mtime). Stores the gathered results in
        self.local_struct

        Args:
            dir (_type_): an absolute path to a root directory
                        for which this function returns lists of
                        contents
        """
        logger.debug('Creating local structure')
        dirs_to_visit = [] # dirs to make OneLocalTier for each
        # --------------- innder func ----------------
        def one_tier_files(parents: str) -> None:
            """gets non resursive contents of one directory, stores
            it into a OneLocalTier object, adds the object to totale result,
            adds directories to dirs_to_visit if there are any

            Args:
                parents (str): relative 'shift' inside the root dir

            Returns: nothing, because modifies variables of parent func
            """
            for_return = OneLocalTier(parents=parents)
            current_dir = path.join(self.local_folder, parents) # get abs path
            # loop over all items in a directory
            for item in listdir(current_dir):
                item_full = path.join(current_dir, item) # get abs path of an item
                # skip links. They are dangerous and not needed on gdrive
                if path.islink(item_full):
                    continue
                # add files as tuples with their modification times with cut off
                # nimbers after a dot
                if path.isfile(item_full):
                    for_return.files.append((item, int(path.getmtime(item_full))))
                    continue
                # add dir to the result and to the list of dirs to visit
                if path.isdir(item_full):
                    for_return.dirs.append(item)
                    dirs_to_visit.append((parents, item))
            self.local_struct.append(for_return)
        # ----------- end innder func ----------------
        # call for the root dir
        one_tier_files('')
        # loop over all other dirs with any nesting inside the root dir
        while dirs_to_visit:
            one_tier_files(path.join(*dirs_to_visit.pop(0)))
        logger.debug('Created local structure')

    def _exclude_ignored(self) -> None:
        """takes both structures self.gdrive_struct and
        self.local_struct and cleans them from objects
        in self.ignored_objects (list[IgnoreThose]) - folders,
        files in a folder or single files. It's important to clean
        both otherwise the objects, presented in one source will be
        copied to another or, even worse, deleted from the first.
        """
        logger.debug('Excluding ignored things')
        # --------------- innder func ----------------
        def exclude_one(
                struct: list[OneGDriveTier]|list[OneLocalTier],
                item_to_exclude: IgnoreThose
        ) -> None:
            """a helper function. Does all the job to exclude stuff

            Args:
                struct (list[OneGDriveTier] | list[OneLocalTier]): a struct
                item_to_exclude (IgnoreThose): item to exclude
            """
            # if we be removing things right in for loor, it probably
            # can be bad for it. So we store the elements
            # (rather labels) and remove later. only for a 'folder'
            items_to_remove = []
            # check if there are items at all
            if not struct:
                return
            # loop over item in a struct
            for item in struct:
                match item_to_exclude.obj_type:
                    # if we should remove just one file
                    case 'single_file':
                        # find the proper item by it's path
                        if item.parents == item_to_exclude.parents:
                            # struct.files are tuples, we have to check first elements
                            for file in item.files:
                                if item_to_exclude.obj_name == file[0]:
                                    # remove and return
                                    item.files.remove(file)
                                    return
                    # ignore all files in some folder
                    case 'all_files':
                        # find the proper item by it's path
                        if item.parents == item_to_exclude.parents:
                            # empty all files
                            item.files.clear()
                            break
                    # ignore a whole folder and it's subfolders with content
                    case 'folder':
                        # remove all subfolders
                        if item_to_exclude.rel_path in item.parents:
                            items_to_remove.append(item)
                        # remove the parent folder from some_tier.dirs
                        if item.tier == item_to_exclude.tier:
                            for dir in item.dirs:
                                if type(dir) is tuple:
                                    if item_to_exclude.obj_name == dir[0]:
                                        item.dirs.remove(dir)
                                        break
                                else:
                                    if item_to_exclude.obj_name == dir:
                                        item.dirs.remove(dir)
                                        break
            # remove ignored folders from a structure
            for item in items_to_remove:
                struct.remove(item)
        # ----------- end innder func ----------------
        # go over all ignoring items
        for item_to_ignore in self.ignored_objects:
            exclude_one(self.gdrive_struct, item_to_ignore)
            exclude_one(self.local_struct, item_to_ignore)  

# ========== manipulate gdrive ===============
    def create_gdrive_folder(self, folder_name: str, parent_folder_id: str|None=None) -> str:
        """creates a folder on gdrive with given name and parent id

        Args:
            folder_name (str): a name of a folder to create
            parent_folder_id (str | None, optional): parent folder id.

        Returns:
            str: newly created forlder id
        """
        logger.info(f'-> Creating folder {folder_name}')
        self.make_creds() # always check
        folder_metadata = {
            'name': folder_name,
            'mimeType': 'application/vnd.google-apps.folder' # type folder
        }
        if parent_folder_id:
            # list is required but more than one item is deprecated
            folder_metadata['parents'] = [parent_folder_id]
        new_folder = self.service.files().create(body=folder_metadata, fields='id').execute()
        return new_folder['id']

    def search_by_name(self,
                       name: str,
                       parent_folder_id: str|None=None,
                       obj_type: Literal['file', 'folder', 'any']='file'
        ) -> list[str]:
        """Searches a given name on google drive, returns a list of
        IDs or an empty list if none was found.

        Args:
            file_name (str): a name of an object to look for, can
                        be partial
            parent_folder_id (str, optional): to search in exact folder.
                        Can be either folder id, root or None to
                        search everywhere
            obj_type (Literal['file', 'folder', 'any'], optional): to search
                        only files or folders, or any type

        Returns:
            list[str]: a list if IDs of found objects
        """

        logger.debug(f'Searching id for {name}')
        self.make_creds() # always check
        # assembling a query
        query = ''
        if parent_folder_id is not None:
            query += f"'{parent_folder_id}' in parents and "
        if obj_type == 'file':
            query += "mimeType!='application/vnd.google-apps.folder' and "
        elif obj_type == 'folder':
            query += "mimeType='application/vnd.google-apps.folder' and "
        query += f"name contains '{name}' and trashed=false"
        results = self.service.files().list(q=query, fields='files(id)').execute()
        for_return = []
        for item in results['files']:
            for_return.append(item['id'])
        return for_return

    def delete_file_or_folder(self, file_id: str) -> None:
        """Deletes an object with said id on gdrive

        Args:
            file_id (str): id of an object to delete
        """
        logger.info(f'x-> Deleting {file_id}')
        self.make_creds()
        try:
            self.service.files().delete(fileId=file_id).execute()
        except HttpError:
            logger.error(f'{file_id} отсутствует')

    def batch_delete_files(self, files_to_delete: list) -> None:
        """Deletes all objects in the list in one request

        Args:
            files_to_delete (list): a list of IDs of objects
                        to delete
        """
        logger.info(f'x-> Batch deleting {files_to_delete}')
        if not files_to_delete:
            return
        self.make_creds()
        batch = self.service.new_batch_http_request()
        for g_id in files_to_delete:
            request = self.service.files().delete(fileId=g_id)
            batch.add(request)
        batch.execute()

    def update_file(self, local_path: str, file_id: str) -> None:
        """Updates the existing gdrive file

        Args:
            local_path (str): path to the file relative to the
                        syncing folder
            file_id (str): id of a file on gdrive
        """
        logger.info(f'-> Updating file {path.basename(local_path)}')
        self.make_creds()
        media = MediaFileUpload(path.join(self.local_folder, local_path), resumable=True)
        self.service.files().update(fileId=file_id, media_body=media).execute()


    def upload_file(self, local_path: str, mtime: float, parent: str='root') -> None:
        """Uploads a new file to gdrive. If a file with such name
        exists, it will be uploaded as a separate file regardless

        Args:
            file_to_upload (str): path to the file relative to the
                        syncing folder
            parent (str, optional): folder id on gdrive where
                        the file will be located
        """
        logger.info(f'-> Uploading file {path.basename(local_path)}')
        self.make_creds()
        # modified_time = datetime.utcfromtimestamp(mtime).replace(tzinfo=timezone.utc).isoformat()
        modified_time = datetime.fromtimestamp(mtime, UTC).isoformat()
        file_metadata = {
            'name': path.basename(local_path),
            'parents': [parent],
            'modifiedTime': modified_time
        }
        media = MediaFileUpload(path.join(self.local_folder, local_path), resumable=True)
        self.service.files().create(body=file_metadata, media_body=media).execute()

    def download_file(self, local_path: str, file_id_to_download: str) -> None:
        """Downloads a file, which exists on gdrive, but not locally.
        Takes it's name from gdrive

        Args:
            file_id_to_download (str): id of a file on gdrive
            local_path (str): a local path where a file should
                        be located, relative to the syncing dir
        """
        self.make_creds()
        # Request the file metadata: kind - file or dir, id, name, mimeType
        # we need name here
        file_metadata = self.service.files().get(fileId=file_id_to_download, fields='modifiedTime,name').execute()
        file_name = file_metadata['name']
        file_mtime = datetime.fromisoformat(file_metadata['modifiedTime']).timestamp()
        file_path_local = path.join(self.local_folder, local_path, file_name)
        # Download the file
        request = self.service.files().get_media(fileId=file_id_to_download)
        # save file to sync folder + inner path + file name
        fh = FileIO(file_path_local, 'wb')
        downloader = MediaIoBaseDownload(fh, request)
        done = False
        while not done:
            status, done = downloader.next_chunk()
            logger.info(f"<- Downloading file {file_name} - {int(status.progress() * 100)}%")
        # set file mtime, otherwise it looks newer than on gdrive
        utime(file_path_local, (file_mtime, file_mtime))
# ======== end manipulate gdrive =============

    def _compare_flat(
            self,
            one_local: OneLocalTier,
            one_gdrive: OneGDriveTier,
            local_dir: str,
        ) -> None:
        """Compares two One...tier objects, and makes all necessary changes
        to reflect local directory to gdrive directory and vice versa

        Args:
            one_local (OneLocalTier): local directory
            one_gdrive (OneGDriveTier): gdrive directory
            local_dir (str): absolute path to the local directory in fs
        """
        logger.debug(f'Comparing dir {one_local.parents if one_local.parents else "root"}')
        files_to_delete = [] # for bacth delete
        # go over all files in a local dir
        while one_local.files:
            local_file, local_mtime = one_local.files.pop()
            # go over all files in a gdrive dir
            for item in one_gdrive.files:
                g_name, g_id, g_mtime = item
                # if the same file name found
                if g_name == local_file:
                    # check if the local file is newer
                    if local_mtime > g_mtime:
                        # if so - update gdrive file
                        self.update_file(path.join(one_local.parents, local_file), g_id)
                    # check if a remote file is newer
                    elif g_mtime > local_mtime:
                        # download it to the folder, consisting of a root dir of syncing folder
                        # and it's relative path inside
                        self.download_file(one_local.parents, g_id)
                    # remove the processed file from gdrive list
                    one_gdrive.files.remove(item)
                    break
            # if a file not found, means it's absent on gdrive
            # thus it should be uploaded if the sync direction is
            # 'local_to_gdrive' or 'mirror' otherwise deleted locally
            else:
                if self.sync_direction in ['local_to_gdrive', 'mirror']:
                    logger.info(f'Local file {path.join(self.local_folder, one_local.parents, local_file)} is '
                        'absent on gdrive')                    
                    self.upload_file(path.join(one_local.parents, local_file), local_mtime, one_gdrive.gparent)
                else:
                    local_file_to_del = path.join(self.local_folder, one_local.parents, local_file)
                    logger.info(f'Deleting local file {local_file_to_del}')
                    remove(local_file_to_del)
        # if anything remins in the list of gdrive files, means these files
        # are absent locally and should be deleted on grdive if sync is
        # 'local_to_gdrive' unless mirror is set. If 'mirror' is set
        # or sync direction is 'gdrive_to_local', than download it
        for item in one_gdrive.files:
            g_name, g_id, g_mtime = item
            if self.sync_direction in ['gdrive_to_local', 'mirror']:
                logger.info(f'File {path.join(one_local.parents, g_name)} is absent locally')
                # download newer file
                self.download_file(one_local.parents, g_id)
            # or delete from gdrive
            else:
                files_to_delete.append(g_id)
        # loop over local dirs
        while one_local.dirs:
            local_dir = one_local.dirs.pop()
            # loop over gdrive dirs
            for item in one_gdrive.dirs:
                g_name, g_id = item
                # if directory exists on gdrive and locally
                # that's good, can stop to search and remove dir
                if g_name == local_dir:
                    one_gdrive.dirs.remove(item)
                    break
            # dir exists locally, but not on gdrive
            else:
                inner_dir_rel_path = path.join(one_local.parents, local_dir)
                # in a case 'local_to_gdrive' or 'mirror we create
                # a folder of current tier and the rest will be created later
                # diring common sync process
                if self.sync_direction in ['local_to_gdrive', 'mirror']:
                    logger.info(f'Dir {inner_dir_rel_path} is absent on gdrive')
                    new_folder = self.create_gdrive_folder(local_dir, one_gdrive.gparent)
                    # new gdrive folder which was created in a process of reflecting
                    # should be added to the gdrive structure; such thing is necessary
                    # because inner tiers of local structure can require it to exist
                    self.gdrive_struct.append(OneGDriveTier(parents=inner_dir_rel_path, gparent=new_folder))
                    # if the only reason for this dir to be created is mirror,
                    # it should be restored locally from gdrive
                    if self.sync_direction != 'local_to_gdrive':
                        self.restore_dirs.append(inner_dir_rel_path)
                # if 'gdrive_to_local' then remove it from local
                else:
                    logger.info(f'Deleting local direcotory tree {inner_dir_rel_path}')
                    rmtree(path.join(self.local_folder, inner_dir_rel_path))
        # deal with remaining gdrive dirs
        while one_gdrive.dirs:
            g_name, g_id = one_gdrive.dirs.pop()
            # delete dirs unless 'mirror' is set
            if self.sync_direction in ['local_to_gdrive', 'mirror']:
                # if set, preserve this directory for further restoration
                if self.sync_direction == 'mirror':
                    mkdir(path.join(self.local_folder, one_gdrive.parents, g_name))
                    self.restore_dirs.append(path.join(one_gdrive.parents, g_name))
                else:
                    files_to_delete.append(g_id)
            # 'gdrive_to_local' and dir exists only on gdrive
            # a folder has to be created
            else:
                dir_to_create = path.join(self.local_folder, one_gdrive.parents, g_name)
                logger.info(f'Dir {dir_to_create} is absent locally, creating')
                mkdir(dir_to_create)
                # maybe not required
                self.local_struct.append(OneLocalTier(path.join(one_gdrive.parents, g_name)))
        # delete all objects marked for this
        if files_to_delete:
            self.batch_delete_files(files_to_delete)
        logger.debug(f'Finished to compare tier {one_local.parents}')

    def sync(self) -> None:
        """Syncs the local and gdrive directory
        """
        # --------------- innder func ----------------
        def tier_maker(
                struct: list[OneGDriveTier]|list[OneLocalTier]
            ) -> dict[int,list[OneGDriveTier]|list[OneLocalTier]]:
            """
            split the structure by it's tiers, where tier -
            is the level of nesting. If 'tires' already contains element
            of a current tier, then add the current one to the list,
            else, add it as a new dict element
            the result be like: tiers = {0: [OneLocalTier obj, OneLocalTier obj],
            1: [OneLocalTier obj], 2: [OneLocalTier obj, OneLocalTier obj]}
            """
            tiers = {}
            for item in struct:
                if item.tier in tiers.keys():
                    tiers[item.tier].append(item)
                else:
                    tiers[item.tier] = [item]     
            return tiers
        # ----------- end innder func ----------------
        logger.debug('Start syncing')
        # this combination looks like apure mistake, prevent data loss
        if self.create_folder and self.sync_direction == 'gdrive_to_local':
            logger.error('A combination of "create folder" and sync "gdrive to local" is not supported! '
                  'It will destroy a data in local folder')
            raise ValueError('"create folder" with sync "gdrive to local" is not supported!')
        # gen local structure
        self._iterate_localdir()
        exists, self.gdrive_folder_id = self._search_sync_dir()
        # a flag to make a new folder on gdrive instead of
        # searching the existing one to sync with
        if self.create_folder and exists:
            parent_dir = self._get_folder_parent(self.gdrive_folder_id)
            self.gdrive_folder = f'{self.gdrive_folder.split("/")[-1]}_{str(int(time()))}'
            self.gdrive_folder_id = self.create_gdrive_folder(self.gdrive_folder, parent_dir)
        # get the gdrive structure
        self._iterate_gdrive(self.gdrive_folder_id)
        # prepare sync_data file for ignoring
        sync_file = IgnoreThose('sync_data.txt', 'single_file')
        # remove all things which should be ignored from both structures
        if self.ignored_objects is not None:
            self.ignored_objects.append(sync_file)
        else:
            self.ignored_objects=[sync_file]
        self._exclude_ignored()
        # depending on the sync direction, we'll be going over
        # local structure or gdrive structure and match the other
        if self.sync_direction == 'local_to_gdrive':
            struct_to_go, struct_to_match = self.local_struct, self.gdrive_struct
        else:
            struct_to_go, struct_to_match = self.gdrive_struct, self.local_struct
        tiers = tier_maker(struct_to_go)
        # go from the top (root) tier to the bottom
        # it will help to cut off unnecessary brancehs
        for item in sorted(tiers.keys()): # loop over tiers starting on top
            for elem in tiers[item]: # loop over every dir on this tier
                for inner_item in struct_to_match: # loop inner folders
                    # when inner folder will be found (and it will be found
                    # if no errors happened, because any absent folder will be created
                    # with the processing of the previous tier)
                    if elem.parents == inner_item.parents:
                        # reflect local structure to the grdive structure
                        if self.sync_direction == 'local_to_gdrive':
                            self._compare_flat(elem, inner_item, self.local_folder)
                        else:
                            self._compare_flat(inner_item, elem, self.local_folder)
                        # delete the processed inner element, so less loops in a future
                        struct_to_match.remove(inner_item)
                        break
        # download/upload remaining folders
        # likely there are none, it's rather rare
        # --------------------------------------
        # here we have the opposide direction of syncing
        # occured because of the mirroring
        # if we have 'local_to_gdrive', it means there is stuff
        # existing only on gdrive and should be downloaded
        # instead of erasing. If we had 'gdrive_to_local',
        # we should upload a folder instead of erasing
        if self.restore_dirs:
            struct_for_restore = []
            # filter those to restore
            # deleted objects aren't filtered out from struct_to_match
            # thus we filter now those which have to be reconstructed
            for item in struct_to_match:
                for rel_path in self.restore_dirs:
                    if rel_path in item.parents:
                        struct_for_restore.append(item)
            # split the new structure to tires
            tiers = tier_maker(struct_for_restore)
            # loop over every tier and every element in it
            # they have to be recreated on the other side
            for item in sorted(tiers.keys()):
                for elem in tiers[item]:
                    logger.info(f'Recreating dir {elem.parents}')
                    # processing the opposite situation, so if general option
                    # is 'local_to_gdrive', then for us now it's 'gdrive_to_local'
                    if self.sync_direction == 'local_to_gdrive':
                        # get all files, remembering that file is a tuple (name, id, mtime)
                        for file in elem.files:
                            self.download_file(elem.parents, file[1])
                        for dir in elem.dirs:
                            mkdir(path.join(self.local_folder, elem.parents, dir[0]))
                    # 'gdrive_to_local', so it's basically 'local_to_gdrive' here
                    else:
                        # have to find a parent dir first.
                        # if there were no issues before, it has to exist
                        for dir in self.gdrive_struct:
                            if dir.parents == elem.parents:
                                parent_dir_id = dir.gparent
                                break
                        for file in elem.files:
                            self.upload_file(path.join(elem.parents, file[0],), file[1], parent_dir_id)
                        for dir in elem.dirs:
                            new_folder = self.create_gdrive_folder(dir, parent_dir_id)
                            self.gdrive_struct.append(OneGDriveTier(parents=path.join(elem.parents, dir), gparent=new_folder))
        logger.debug(f'Finish syncing')

def sendmessage(message: str='', timeout: str='0') -> None:
    """Sends a message to notification daemon in a separate process.
    urgency=critical makes a message stay until closed manually,
    for other message types types don't forget timeout"""
    try:
        if os_name == 'posix':
            subprocess.Popen(['notify-send', '-i', './icons/gdrive.png', '-t', timeout, 'gdrive sync', message])
        else:
            from win10toast import ToastNotifier
            toaster = ToastNotifier()
            toaster.show_toast('gdrive sync', message, icon_path='./icons/gdrive.ico', duration=3, threaded=True)
    except (FileNotFoundError, ModuleNotFoundError):
        logger.error('No program to show messages or win10toast module')

def ignore_directory_parser(arg_string: str) -> IgnoreThose:
    """Parses the input arguments like path=<path>,type=<type>

    Args:
        arg_string (str): string containing arguments

    Raises:
        ArgumentTypeError: when arguments are in given
                    in wrong format

    Returns:
        IgnoreThose: a class instance with proper fields
    """
    rel_path = ''
    action_type = ''
    try:
        # split path and type
        ignore_items = arg_string.split(',')
        for item in ignore_items:
            # split items around "="
            item_parts = item.split('=')
            if item_parts[0] == 'path':
                rel_path = item_parts[1]
            elif item_parts[0] == 'type':
                action_type = item_parts[1]
        # if both parameters are found and action type is one of the values
        if rel_path and action_type and action_type in ['single_file', 'all_files', 'folder']:
            return IgnoreThose(rel_path, action_type)
    # the exception type doesn't matter here, it's pure usage mistake
    # so in a case return didn't happen, something wrong with input values
    except:
        pass
    raise ArgumentTypeError('Wrong usage, example: --ignore path=<path>,'
                            'type=<type> --ignore path=<path>,type=<type>')

if __name__ == '__main__':
    logger = logging.getLogger('mylogger')
    logger.setLevel(logging.DEBUG)
    formatter = logging.Formatter(
        '{asctime} [{levelname:8}] {message}',
        datefmt='%Y-%m-%d %H:%M:%S',
        style='{'
        )
    # make two handlers to have an output in both - file and terminal
    term_handler = logging.StreamHandler()
    file_handler = logging.FileHandler('sync.log', mode='a', encoding=None, delay=False)
    term_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)
    logger.addHandler(term_handler)
    logger.addHandler(file_handler)

    retries = 3 # three attempts to sync, in case of network issues
    parser = ArgumentParser()
    parser.add_argument('local_path', type=str, help='full path to a local directory')
    parser.add_argument('gdrive_dir',type=str,
        help='filesystem-like path on gdrive. Same pattern as for local directory')
    # if a new gdrive folder should be created regardless of it's existance
    parser.add_argument(
        "-n",
        "--new",
        action="store_true",
        help='If set, a new folder on gdrive will be created for syncing'
    )
    parser.add_argument('--sync-direction', choices=['local_to_gdrive', 'gdrive_to_local', 'mirror'],
                        default='local_to_gdrive', help='options to use:'
                        'local_to_gdrive, gdrive_to_local, mirror')
    parser.add_argument('--ignore', type=ignore_directory_parser, action='append',
                    help='ignore directories with the specified path and type.'
                    'Format: --ignore path=<path>,type=<type> '
                    '--ignore path=<path>,type=<type> ... .'
                    '<type>: single_file, all_files, folder'
                    '<path>: RELATIVE path INSIDE the syncing directory')
    args = parser.parse_args()
    logger.debug(f'syncing with arguments: local dir - {args.local_path}, '
                 f'gdrive dir - {args.gdrive_dir}, '
                 f'sync direction {args.sync_direction}' + 
                 (', create new dir' if args.new else '') +
                 (', ignored objects - ' + '; '.join([
                     f'path={x.rel_path},type={x.obj_type}' for x in args.ignore
                 ]) if args.ignore else ''))
    if path.exists(args.local_path):
        while retries:
            try:
                gdrive = GdriveSync(
                    **GOOGLE_LOGIN,
                    local_folder=args.local_path,
                    gdrive_folder=args.gdrive_dir,
                    create_folder=args.new,
                    sync_direction=args.sync_direction,
                    ignored_objects=args.ignore
                )
                gdrive.sync()
                sendmessage(f'{args.gdrive_dir} successfully synced', '10000')
                logger.info('All done well\n-----------------------')
                break # the work is done
            # if issues are related exactly to the network then wait and retry
            except (TimeoutError, TransportError, ServerNotFoundError, RefreshError):
                sendmessage(f'{args.gdrive_dir} wasnt synced, probably network issues, will retry', '10000')
                logger.error('Network error, retrying')
                sleep(120)
                retries -= 1
            except Exception as e:
                logger.error('Unexpected error, interrupted')
                sendmessage(f'{args.gdrive_dir} wasnt synced, an error occured: {str(e)}')
                break
        else:
            logger.critical('Network error, out of retries')
            sendmessage(f'{args.gdrive_dir} wasnt synced, probably network issues, retries are over')
    else:
        logger.error('No local folder')
        sendmessage(f'{args.local_path} doesnt exist locally')
