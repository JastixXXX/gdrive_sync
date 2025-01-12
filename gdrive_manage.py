# This scrypt is for syncing a local directory with a directory on
# Google Drive. Takes these arguments:
# Required:
# 1. The local directory absolute path.
# 2. The google drive os-like path, i.e. a path relative to the
# Google Drive root <foldername>/<innerfolder>/...
# Optional:
# 1. A list of objects to not sync. --ignore path=<somepath>,type=<ignoretype>
# where "somepath" is relative path inside the syncing directory and
# ignoretype can be "single_file", "all_files", "folder" which covers
# all cases
# 2. -n --new flag. A new gdrive directory will be created instead of
# searching an existing one. If there is an existing one with such name,
# the new one will be created with slightly different name
# 3. --sync-direction handles file deletions. It has four
# options: "gdrive_to_local", "local_to_gdrive", "mirror", "ask"
# --------
# new mode - partial update. Instead of --sync-direction expects these
# arguments '--mode' 'partial_update' '--actions_json' '{
#    'delete_dir': ['gdrive/to/dir1', ...],
#    'delete_file': [...],
#    'create_dir': [...],
#    'create_file': ['local/path/file1', ...],
#    'update_file': [...],
#    'rename': {'local/path/old_name: local/path/new_name', ...},
#    'move': {'local/path/old_name: local/path/new_name', ...}
# }'
# This mode doesn't respect --ignore and just fullfills the actions
# listed in --actions_json

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
# A new option was added - "ask". Unlike "gdrive_to_local" and
# "local_to_gdrive", the script will interactively ask user what
# to do with differences in the catalog structure. Either "c" to
# create an absent file or "r" to remove the difference.

import logging
import subprocess
import sys
import json
from os import path, listdir, remove, mkdir, utime, walk
from os import name as os_name
from os import sep as os_sep
from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google.auth.exceptions import TransportError, RefreshError
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from googleapiclient.http import MediaFileUpload, MediaIoBaseDownload
from io import FileIO
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

# ========= special for pyinstaller ==========
def resource_path(relative_path, outer_file: bool=False):
    """Get the absolute path to the resource,
    works for dev and for PyInstaller
    
    outer_file if True - means that a file should be looked for
    not in the pyinstaller bundle but next to the executable.
    Does nothing for non pyinstaller env"""
    try:
        # PyInstaller creates a temporary folder named _MEIPASS
        base_path = sys._MEIPASS
        # if we don't need the MEIPASS directory
        if outer_file:
            base_path = path.dirname(sys.executable)
    # if no _MEIPASS, no pyinstaller
    except Exception:
        base_path = path.abspath(".")
    return path.join(base_path, relative_path)
# ======== end special for pyinstaller========

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
        self.rel_path = path.normpath(rel_path)
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
        else:
            self.tier = len(path.normpath(parents).split(os_sep))


class OneGDriveTier(OneLocalTier):
    """this class is meant to store lists of filenames and
    directory names in some direcorty and parents on gdrive
    """
    def __init__(self, parents: str='', gparent: str='') -> None:
        """
        Takes two more parameters:

        "gparent" for gdrive items only, because they have relative path which is
        for a user and parent folder id, which is for API requests

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
        sync_direction: Literal['local_to_gdrive', 'gdrive_to_local', 'mirror', 'ask']='local_to_gdrive',
        ignored_objects: list[IgnoreThose]|None = None
    ) -> None:
        # don't forget to get the actual path from pyinstalled files
        self.client_secrets_file = resource_path(client_secrets_file, True)
        self.token_file = resource_path(token_file, True)
        self.scopes = scopes
        # folder name gdrive given by it's human readable path
        self.gdrive_folder = path.normpath(gdrive_folder)
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

    def _search_sync_dir(
            self,
            gdrive_path: str,
            gdrive_dir_id_cache: dict|None=None,
            dont_create_chain: bool=False,
            vault_dir: bool=False
        ) -> tuple:
        """searches a directory on gdrive by a given path, if doesn't
        find it, creates a new one. Returns the directory id in any case

        Args:
            gdrive_path (str): path to the gdrive dir, liiks like
                        /dir/dir/targetdir or \\dir\\dir\\targetdir
            gdrive_dir_id_cache (dict): was added with update_partial mode.
                        The side effect will be used, by modifying the dict
                        by it's ref. First looks there, then actually searches
            dont_create_chain (bool): was added with update_partial mode.
                        The function won't create absent dirs
            vault_dir (bool): to separate if looking for a dir to operate
                        with or for a root vault dir. For logging
        Returns:
            tuple: a tuple, consists of two values - boolean, which is set
                        to True if the directory was found on gdrive and
                        False if created, and str - the directory id
        """
        # remove innecessary dir separators
        gdrive_path = path.normpath(gdrive_path)
        logger.info(f'Searching{" VAULT" if vault_dir else ""} directory {gdrive_path} on gdrive')
        self.make_creds() # always check
        dir_exists = True # init with assumption we'll find the dir
        # gdrive doesn't support os-like paths, so we have to check
        # the existence of every item in the path chain
        folder_chain = gdrive_path.split(os_sep)
        parent_folder_id = 'root' # search start point
        # for gdrive_dir_id_cache keys
        ready_chain = ''
        while folder_chain:
            folder_name = folder_chain.pop(0) # get the topmost element
            ready_chain = path.join(ready_chain, folder_name)
            # search among saved ids
            if gdrive_dir_id_cache is not None and ready_chain in gdrive_dir_id_cache:
                results = gdrive_dir_id_cache[ready_chain]
            else:
                # query to request a folder with required name and parent
                results = self.search_by_name(name=folder_name, parent_folder_id=parent_folder_id, obj_type='folder')
            # if found, then we can go deeper by the chain
            if results:
                # notify if there are more than one dir with teh same name
                parent_folder_id = results[0]
                if len(results) > 1:
                    logger.info(f'(gdrive) !!! warning, found several directories {folder_name} on gdrive')
                # save if our "cache" is used, no  problem if rewrite
                if gdrive_dir_id_cache is not None:
                    gdrive_dir_id_cache[ready_chain] = results
            # if not found, then create the rest of the absent chain
            else:
                dir_exists = False
                # put back the removed above item, since we didn't find it
                folder_chain.insert(0, folder_name)
                # simply create all absent, if dont_create_chain isn't used
                if not dont_create_chain:
                    for item in folder_chain:
                        parent_folder_id = self.create_gdrive_folder(item, parent_folder_id)
                        if gdrive_dir_id_cache is not None:
                            ready_chain = path.join(ready_chain, item)
                            gdrive_dir_id_cache[ready_chain] = parent_folder_id
                    break
        # log if found. If it was created - another function logs it
        if dir_exists:
            logger.info(f'Found{" VAULT" if vault_dir else ""} directory {gdrive_path} on gdrive')
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
        # clear self.ignored_objects for usage in 'ask' sync direction
        self.ignored_objects.clear()

# ========== manipulate gdrive ===============
    def create_gdrive_folder(self, folder_name: str, parent_folder_id: str|None=None) -> str:
        """creates a folder on gdrive with given name and parent id

        Args:
            folder_name (str): a name of a folder to create
            parent_folder_id (str | None, optional): parent folder id.

        Returns:
            str: newly created forlder id
        """
        logger.info(f'[+](gdrive) creating folder {folder_name}')
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
            file_name (str): a name of an object to look for, can not
                        be partial
            parent_folder_id (str, optional): to search in exact folder.
                        Can be either folder id, root or None to
                        search everywhere
            obj_type (Literal['file', 'folder', 'any'], optional): to search
                        only files or folders, or any type

        Returns:
            list[str]: a list if IDs of found objects
        """

        logger.debug(f'(gdrive) searching id for {name}')
        self.make_creds() # always check
        # assembling a query
        query = ''
        if parent_folder_id is not None:
            query += f"'{parent_folder_id}' in parents and "
        if obj_type == 'file':
            query += "mimeType!='application/vnd.google-apps.folder' and "
        elif obj_type == 'folder':
            query += "mimeType='application/vnd.google-apps.folder' and "
        # query += f"name contains '{name}' and trashed=false"
        # looking for the exact name instead of partial
        query += f"name = '{name}' and trashed=false"
        results = self.service.files().list(q=query, fields='files(id)').execute()
        for_return = []
        for item in results['files']:
            for_return.append(item['id'])
        return for_return

    def delete_file_or_folder(self, file_id: str, file_name: str) -> None:
        """Deletes an object with said id on gdrive

        Args:
            file_id (dict): id and path of an object to delete
        """
        logger.info(f'x(gdrive) deleting {file_name}')
        self.make_creds()
        try:
            self.service.files().delete(fileId=file_id).execute()
        except HttpError:
            logger.error(f'{file_id} отсутствует')

    def batch_delete_files(self, files_to_delete: dict[str, str]) -> None:
        """Deletes all objects in the list in one request

        Args:
            files_to_delete (dict): a list of IDs and paths
                        of objects to delete
        """
        if not files_to_delete:
            return
        logger.info(f'x(gdrive) batch deleting {", ".join(files_to_delete.values())}')
        self.make_creds()
        batch = self.service.new_batch_http_request()
        for g_id in files_to_delete.keys():
            request = self.service.files().delete(fileId=g_id)
            batch.add(request)
        batch.execute()

    def update_file(self, local_path: str, file_id: str, mtime: int=0) -> None:
        """Updates the existing gdrive file, preserving it's
        modification time

        Args:
            local_path (str): path to the file relative to the
                        syncing folder
            file_id (str): id of a file on gdrive
        """
        logger.info(f'(local) -> (gdrive) updating file {path.basename(local_path)}')
        self.make_creds()
        # full_path = path.join(self.local_folder, local_path)
        media = MediaFileUpload(path.join(self.local_folder, local_path), resumable=True)
        # Get the current modification time of the local file
        if not mtime:
            mtime = int(path.getmtime(local_path))     
        mtime_iso = datetime.fromtimestamp(mtime, UTC).isoformat()   
        # Update the file metadata and media
        self.service.files().update(
            fileId=file_id,
            media_body=media,
            body={
                'modifiedTime': mtime_iso
            }
        ).execute()

    def rename_file_or_folder(self, file_id: str, new_name: str, local_path: str) -> None:
        """Renames an existing gdrive file or folder

        Args:
            file_id (str): gdrive id of a file or a dir to rename
            new_name (str): new name for this file or dir, with it's
                        relative path
            local_path (str): local path to the renaming object.
                        Solely for the logging purpose
        """
        logger.info(f'(gdrive) renaming {local_path} to {new_name}')
        self.make_creds()
        # Specify the new name in the metadata
        file_metadata = {'name': path.basename(new_name)}
        # Use the 'update' method to rename the file or folder
        self.service.files().update(
            fileId=file_id,
            body=file_metadata,
            fields='id, name'
        ).execute()

    # Function to move a file or folder
    def move_file_or_folder(self, file_id: str, new_parent_id: str, old_path: str, new_path: str) -> None:  
        """Moves an existing gdrive file or folder

        Args:
            file_id (str): gdrive id of a file or a dir to rename
            new_parent_id (str): directory id where to put files/dirs
            old_path, new_path (str): old and new path for an object.
                        Solely for the logging purpose
        """           
        logger.info(f'<->(gdrive) moving {old_path} to {new_path}')
        self.make_creds()
        # Retrieve the existing parent folder IDs
        file = self.service.files().get(
            fileId=file_id,
            fields='parents'
        ).execute()
        # tbh I didn't see the parents array containing more that one element, ever
        current_parents = ",".join(file.get('parents'))
        # Move the file or folder to the new parent folder
        self.service.files().update(
            fileId=file_id,
            addParents=new_parent_id,
            removeParents=current_parents,
            fields='id, parents'
        ).execute()

    def upload_file(self, local_path: str, mtime: int=0, parent: str='root') -> None:
        """Uploads a new file to gdrive. If a file with such name
        exists, it will be uploaded as a separate file regardless

        Args:
            file_to_upload (str): path to the file relative to the
                        syncing folder
            parent (str, optional): folder id on gdrive where
                        the file will be located
        """
        logger.info(f'(local) -> (gdrive) uploading file {local_path}')
        self.make_creds()
        full_local_path = path.join(self.local_folder, local_path)
        if not mtime:
            mtime = int(path.getmtime(full_local_path))
        mtime_iso = datetime.fromtimestamp(mtime, UTC).isoformat()
        # mtime_iso = datetime.fromtimestamp(mtime).isoformat(timespec='seconds') + 'Z'  # Convert to RFC3339 format 
        file_metadata = {
            'name': path.basename(local_path),
            'parents': [parent],
            'modifiedTime': mtime_iso
        }
        media = MediaFileUpload(full_local_path, resumable=True)
        self.service.files().create(body=file_metadata, media_body=media).execute()

    def upload_folder(self, local_path, parent='root') -> None:
        """Uploads a whole dir to gdrive. If a dir with such name
        exists, it will be uploaded as a separate dir regardless

        Args:
            local_path (str): path to the dir relative to the
                        syncing folder
            parent (str, optional): folder id on gdrive where
                        the dir will be located
        """
        logger.info(f'(local) [->] (grdive) uploading directory {local_path}')
        self.make_creds()
        full_local_path = path.join(self.local_folder, local_path)
        folder_ids = {full_local_path: self.create_gdrive_folder(path.basename(local_path), parent)}
        for root, dirs, files in walk(full_local_path):
            for directory in dirs:
                dir_path = path.join(root, directory)
                parent_path = path.dirname(dir_path)
                parent_id = folder_ids[parent_path]
                folder_ids[dir_path] = self.create_gdrive_folder(directory, parent_id)
            for file in files:
                file_path = path.join(root, file)
                parent_id = folder_ids[root]
                self.upload_file(file_path, parent=parent_id)

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
            logger.info(f"(local) <- (gdrive) downloading file {file_name} - {int(status.progress() * 100)}%")
        # set file mtime, otherwise it looks newer than on gdrive
        utime(file_path_local, (file_mtime, file_mtime))
# ======== end manipulate gdrive =============

    @staticmethod
    def _ask_user_create(
            filepath: str,
            absent_locally: bool,
            file_is_dir: bool=False
        ) -> bool:
        """Creates a message, that an action with file is required
        and awaits for a proper user input

        Args:
            filepath (str): absent file path
            absent_locally (bool): where absent
            file_is_dir (bool, optional): the absent file is dir. Defaults to False.
        Returns:
            True if a file should be created, False otherwise
        """
        user_input = None
        while not user_input in ['c', 'r']:
            user_input = input(f'{"(?) Directory" if file_is_dir else "(?) File"} "{filepath}" is ABSENT '
                               f'{"LOCALLY" if absent_locally else "ON GDRIVE"}. Input '
                               f'"c" to create the absent {"directory" if file_is_dir else "file"} '
                               f'or "r" to remove the existing one: ')
        logger.info(f'(?) User was asked about {"directory" if file_is_dir else "file"} "{filepath}", '
                    f'which is absent {"locally" if absent_locally else "on gdrive"}. '
                    f'Decision was {"CREATE" if user_input == 'c' else "DELETE"} '
                    f'this {"directory" if file_is_dir else "file"}')
        # user_input will contain only one of these two values
        return True if user_input == 'c' else False

    def _compare_flat(
            self,
            one_local: OneLocalTier,
            one_gdrive: OneGDriveTier,
        ) -> None:
        """Compares two One...tier objects, and makes all necessary changes
        to reflect local directory to gdrive directory and vice versa

        Args:
            one_local (OneLocalTier): local directory
            one_gdrive (OneGDriveTier): gdrive directory
        """
        logger.debug(f'Comparing dir {one_local.parents if one_local.parents else "root"}')
        files_to_delete = {} # for bacth delete
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
                        self.update_file(path.join(one_local.parents, local_file), g_id, local_mtime)
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
            # 'local_to_gdrive' or 'mirror' or user clicked 'c'.
            # if user cliecked 'r' or direction is 'gdrive_to_local' - 
            # deleted locally
            else:
                local_rel_file_path = path.join(one_local.parents, local_file)
                # ask for the user input, if True - create a file
                if self.sync_direction == 'ask':
                    user_action = self._ask_user_create(local_rel_file_path, absent_locally=False)
                if (self.sync_direction in ['local_to_gdrive', 'mirror'] or
                    (self.sync_direction == 'ask' and user_action)):
                    logger.info(f'Local file {local_rel_file_path} is absent on gdrive')                    
                    self.upload_file(path.join(one_local.parents, local_file), local_mtime, one_gdrive.gparent)
                else:
                    logger.info(f'x(local) deleting local file {local_rel_file_path}')
                    remove(path.join(self.local_folder, one_local.parents, local_file))
        # if anything remins in the list of gdrive files, means these files
        # are absent locally and should be deleted on grdive if sync is
        # 'local_to_gdrive'. If direction is'mirror' or 'gdrive_to_local' or
        # 'ask' with user desire to create files, than download it
        for item in one_gdrive.files:
            g_name, g_id, g_mtime = item
            gdrive_rel_file_path = path.join(one_gdrive.parents, g_name)
            # ask for the user input, if True - create a file
            if self.sync_direction == 'ask':
                user_action = self._ask_user_create(gdrive_rel_file_path, absent_locally=True)
            if (self.sync_direction in ['gdrive_to_local', 'mirror'] or
                (self.sync_direction == 'ask' and user_action)):
                logger.info(f'File {gdrive_rel_file_path} is absent locally')
                # download newer file
                self.download_file(one_gdrive.parents, g_id)
            # or delete from gdrive
            else:
                files_to_delete[g_id] = gdrive_rel_file_path
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
                local_rel_dir_path = path.join(one_local.parents, local_dir)
                # ask for the user input, if True - create a file
                if self.sync_direction == 'ask':
                    user_action = self._ask_user_create(local_rel_dir_path, absent_locally=False, file_is_dir=True)
                # in a case 'local_to_gdrive', 'mirror' or 'ask' with user
                # desire to create the dir we create a folder of current tier
                # and the rest will be created later diring common sync process
                if (self.sync_direction in ['local_to_gdrive', 'mirror'] or
                    (self.sync_direction == 'ask' and user_action)):
                    logger.info(f'Dir {local_rel_dir_path} is absent on gdrive')
                    new_folder = self.create_gdrive_folder(local_dir, one_gdrive.gparent)
                    # new gdrive folder which was created in a process of reflecting
                    # should be added to the gdrive structure; such thing is necessary
                    # because inner tiers of local structure can require it to exist
                    self.gdrive_struct.append(OneGDriveTier(parents=local_rel_dir_path, gparent=new_folder))
                    # if the reason for this dir to be created is mirror or ask,
                    # it should be restored locally from gdrive
                    if self.sync_direction != 'local_to_gdrive':
                        self.restore_dirs.append(local_rel_dir_path)
                # if 'gdrive_to_local' or 'ask' with desire to remove - remove it from local
                else:
                    logger.info(f'[x](local) deleting local direcotory tree {local_rel_dir_path}')
                    rmtree(path.join(self.local_folder, local_rel_dir_path))
        # deal with remaining gdrive dirs
        while one_gdrive.dirs:
            g_name, g_id = one_gdrive.dirs.pop()
            # if 'local_to_gdrive' or 'ask' with user desire to delete
            # delete those dirs on gdrive
            # --------------------- old -----------------
            # if self.sync_direction in ['local_to_gdrive', 'mirror']:
            #     # if set, preserve this directory for further restoration
            #     if self.sync_direction == 'mirror':
            #         mkdir(path.join(self.local_folder, one_gdrive.parents, g_name))
            #         self.restore_dirs.append(path.join(one_gdrive.parents, g_name))
            #     else:
            #         files_to_delete.append(g_id)
            # # 'gdrive_to_local' and dir exists only on gdrive
            # # a folder has to be created
            # else:
            #     dir_to_create = path.join(self.local_folder, one_gdrive.parents, g_name)
            #     logger.info(f'Dir {dir_to_create} is absent locally, creating')
            #     mkdir(dir_to_create)
            #     # maybe not required
            #     self.local_struct.append(OneLocalTier(path.join(one_gdrive.parents, g_name)))
            # --------------------- old ----------------- 
            gdrive_rel_dir_path = path.join(one_gdrive.parents, g_name)  
            # ask for the user input, if True - create a file
            if self.sync_direction == 'ask':
                user_action = self._ask_user_create(gdrive_rel_dir_path, absent_locally=True, file_is_dir=True) 
            if (self.sync_direction == 'local_to_gdrive' or
                (self.sync_direction == 'ask' and not user_action)):
                files_to_delete[g_id] = gdrive_rel_dir_path
            # dir should be created locally
            else:
                logger.info(f'[+](local) directory {gdrive_rel_dir_path} is absent locally, creating')
                mkdir(path.join(self.local_folder, one_gdrive.parents, g_name))
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
        # this combination looks like a pure mistake, prevent data loss
        if self.create_folder and self.sync_direction == 'gdrive_to_local':
            logger.error('A combination of "create folder" and sync "gdrive to local" is not supported! '
                  'It will destroy all data in the local folder')
            raise ValueError('"create folder" with sync "gdrive to local" is not supported!')
        # gen local structure
        self._iterate_localdir()
        exists, self.gdrive_folder_id = self._search_sync_dir(self.gdrive_folder, vault_dir=True)
        # a flag to make a new folder on gdrive instead of
        # searching the existing one to sync with
        if self.create_folder and exists:
            parent_dir = self._get_folder_parent(self.gdrive_folder_id)
            self.gdrive_folder = f'{path.basename(self.gdrive_folder)}_{str(int(time()))}'
            self.gdrive_folder_id = self.create_gdrive_folder(self.gdrive_folder, parent_dir)
        # get the gdrive structure
        self._iterate_gdrive(self.gdrive_folder_id)
        # remove ignored files
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
                            self._compare_flat(elem, inner_item)
                        else:
                            self._compare_flat(inner_item, elem)
                        # delete the processed inner element, so less loops in a future
                        struct_to_match.remove(inner_item)
                        break
        # download/upload remaining folders
        # likely there are none, it's rather rare
        # --------------------------------------
        # here we have the opposide direction of syncing
        # occured because of the mirroring or 'ask'
        # if we have 'local_to_gdrive', it means there is stuff
        # existing only on gdrive and should be downloaded
        # instead of erasing. Otherwise, we should upload
        # a folder instead of erasing
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
                    logger.info(f'Restoring dir structure {elem.parents}')
                    # --------------------- old -----------------
                    # # processing the opposite situation, so if general option
                    # # is 'local_to_gdrive', then for us now it's 'gdrive_to_local'
                    # if self.sync_direction == 'local_to_gdrive':
                    #     # get all files, remembering that file is a tuple (name, id, mtime)
                    #     for file in elem.files:
                    #         self.download_file(elem.parents, file[1])
                    #     for dir in elem.dirs:
                    #         mkdir(path.join(self.local_folder, elem.parents, dir[0]))
                    # # 'gdrive_to_local', so it's basically 'local_to_gdrive' here
                    # else:
                    #     # have to find a parent dir first.
                    #     # if there were no issues before, it has to exist
                    #     for dir in self.gdrive_struct:
                    #         if dir.parents == elem.parents:
                    #             parent_dir_id = dir.gparent
                    #             break
                    #     for file in elem.files:
                    #         self.upload_file(path.join(elem.parents, file[0],), file[1], parent_dir_id)
                    #     for dir in elem.dirs:
                    #         new_folder = self.create_gdrive_folder(dir, parent_dir_id)
                    #         self.gdrive_struct.append(OneGDriveTier(parents=path.join(elem.parents, dir), gparent=new_folder))
                    # --------------------- old -----------------
                    # have to find a parent dir first.
                    # if there were no issues before, it has to exist
                    for dir in self.gdrive_struct:
                        if dir.parents == elem.parents:
                            parent_dir_id = dir.gparent
                            break
                    for file in elem.files:
                        # ask for the user input, if True - create a file
                        if self.sync_direction == 'ask':
                            if not self._ask_user_create(path.join(elem.parents, file[0]), absent_locally=False, file_is_dir=False):
                                continue
                        self.upload_file(path.join(elem.parents, file[0],), file[1], parent_dir_id)
                    for dir in elem.dirs:                        # ask for the user input, if True - create a file
                        if self.sync_direction == 'ask':
                            if not self._ask_user_create(path.join(elem.parents, file[0]), absent_locally=False, file_is_dir=True):
                                continue
                        new_folder = self.create_gdrive_folder(dir, parent_dir_id)
                        self.gdrive_struct.append(OneGDriveTier(parents=path.join(elem.parents, dir), gparent=new_folder))
        logger.debug(f'Finish syncing')

    def sync_partial(self, actions_json: str) -> None:
        """Applies to gdrive accumulated partial updates.
        Performs given actions when possible with no checks,
        so it's the responsibility of the data to be not
        contradictory

        Args:
            actions_json(str): json string like this
            {
              'delete_dir': ['gdrive/to/dir1', ...],
              'delete_file': [...],
              'create_dir': [...],
              'create_file': ['local/path/file1', ...],
              'update_file': [...],
              'rename': {'local/path/old_name: local/path/new_name', ...},
              'move': {'local/path/old_name: local/path/new_name', ...}
            }            
        """
        # if there will be an error, it will be caught in __main__
        actions = json.loads(actions_json)
        # we won't do any optimisations like for full sync, because
        # actions is assumed to be relatively small, a few files in average

        # get the existing gdrive directory or create a new one.
        # in theory it makes not much sense, but may be usable
        # for newly created Vault

        # going to also save gdrive found dir ids to prevent unnecessary requests
        gdrive_dir_id_cache = {}
        exists, self.gdrive_folder_id = self._search_sync_dir(
            self.gdrive_folder,
            gdrive_dir_id_cache=gdrive_dir_id_cache,
            vault_dir=True
        )
        # first makes sense to create dirs
        if 'create_dir' in actions:
            for dir in actions['create_dir']:
                self._search_sync_dir(path.join(self.gdrive_folder, dir), gdrive_dir_id_cache=gdrive_dir_id_cache)
        # now - delete dirs
        if 'delete_dir' in actions:
            for dir in actions['delete_dir']:
                # search directory on gdrive, don't create if absent
                exists, dir_id = self._search_sync_dir(
                    path.join(self.gdrive_folder, dir),
                    gdrive_dir_id_cache=gdrive_dir_id_cache,
                    dont_create_chain=True
                )
                # if the directory exists at all
                if exists:
                    # delete on gdrive
                    self.delete_file_or_folder(dir_id, dir)
                    # delete this exact dir from "cache" and all other dirs
                    # which lay inside the one which will be deleted
                    gdrive_dir_id_cache = { k: v for k, v in gdrive_dir_id_cache.items() if not dir in k }
        # now delete files. Those which remain after the directory deletion
        # we are going to accumulate them to batch delete
        if 'delete_file' in actions:
            files_to_del = {}
            for file in actions['delete_file']:
                # search a directory on gdrive, which contains
                # the file. Don't create the dir if absent
                exists, dir_id = self._search_sync_dir(
                    path.join(self.gdrive_folder, path.dirname(file)),
                    gdrive_dir_id_cache=gdrive_dir_id_cache,
                    dont_create_chain=True
                )
                # if the directory exists, look for a file
                if exists:
                    file_id = self.search_by_name(path.basename(file), dir_id, 'file')
                    # if file exists, add it to the del list
                    if file_id:
                        if len(file_id) > 1:
                            logger.info(f'(gdrive) !!! warning, found several files {file} on gdrive')
                        files_to_del[file] = file_id[0]
            # del files
            self.batch_delete_files(files_to_del)
        # move existing files/dirs
        if 'move' in actions:
            for file in actions['move']:
                # search a directory on gdrive, which contains
                # the file. Don't create the dir if absent
                old_exists, old_dir_id = self._search_sync_dir(
                    path.join(self.gdrive_folder, path.dirname(file)),
                    gdrive_dir_id_cache=gdrive_dir_id_cache,
                    dont_create_chain=True
                )
                # if the directory exists, look for a file/dir
                if old_exists:
                    file_id = self.search_by_name(path.basename(file), old_dir_id, 'any')
                # get new parent id create the dir if absent
                _, new_dir_id = self._search_sync_dir(
                    path.join(self.gdrive_folder, path.dirname(actions['move'][file])),
                    gdrive_dir_id_cache=gdrive_dir_id_cache
                )    
                # if file/dir exists, move it, otherwise upload from the pc
                if file_id:    
                    if len(file_id) > 1:
                        logger.info(f'(gdrive) !!! warning, found several files {file} on gdrive')                
                    self.move_file_or_folder(file_id[0], new_dir_id, file, actions['move'][file])
                else:
                    # now upload depending what is it - a dir or a file
                    if path.isdir(path.join(self.local_folder, file)):
                        self.upload_folder(file, new_dir_id)
                    else:
                        self.upload_file(file, parent=new_dir_id)       
        # now create or update files. Gdrive allows to have files
        # with same names in one directory, but pc filesystems usually
        # don't. So we'll be looking even for "create" files and update
        # them, create only if absent. Rename the same thing. We'll be
        # uploading such files if absent
        create_update_files = []
        for act in ['create_file', 'update_file']:
            if act in actions:
                create_update_files += actions[act]    
        # rename can be applied to both - files and dirs and
        # contains a dict instead of a list where keys - old names
        # and values - new names
        for_rename = []
        if 'rename' in actions and isinstance(actions['rename'], dict):
            # save it for easier checks
            for_rename = list(actions['rename'].keys())
            create_update_files += for_rename
        for file in create_update_files:
            # search a directory on gdrive, which contains
            # the file. Create the dir if absent, though it
            # should be already created before
            exists, dir_id = self._search_sync_dir(
                path.join(self.gdrive_folder, path.dirname(file)),
                gdrive_dir_id_cache=gdrive_dir_id_cache
            )
            # look for a file
            file_id = self.search_by_name(path.basename(file), dir_id, 'any')
            # if file exists - update or rename it.
            # we take the 0-th item assuming there shouldn't be more with the same name
            # we also don't check if this file isn't newer than the existing one, we got 
            # the request to upload/rename and we do it
            if file_id:
                if len(file_id) > 1:
                    logger.info(f'(gdrive) !!! warning, found several files {file} on gdrive')
                # check what to do - update or rename
                if file in for_rename:
                    self.rename_file_or_folder(file_id[0], actions['rename'][file], file)
                else:
                    self.update_file(file, file_id[0])
            # otherwise - upload
            else:
                self.upload_file(file, parent=dir_id)        


def sendmessage(message: str='', timeout: str='0') -> None:
    """Sends a message to notification daemon in a separate process.
    urgency=critical makes a message stay until closed manually,
    for other message types types don't forget timeout"""
    try:
        icons_dir = resource_path('icons')
        if os_name == 'posix':
            subprocess.Popen(['notify-send', '-i', f'{icons_dir}/gdrive.png', '-t', timeout, 'gdrive sync', message])
        else:
            from win10toast import ToastNotifier
            toaster = ToastNotifier()
            toaster.show_toast('gdrive sync', message, icon_path=f'{icons_dir}\\gdrive.ico', duration=3, threaded=True)
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
    # make three handlers to have an output in both - file and terminal
    # and split the terminal output to stdout and stderr. StreamHandler
    # by default outputs everything to stderr
    file_handler = logging.FileHandler('sync.log', mode='a', encoding=None, delay=False)
    file_handler.setFormatter(formatter)
    logger.addHandler(file_handler)
    # Handler for stdout
    stdout_handler = logging.StreamHandler(sys.stdout)
    stdout_handler.setLevel(logging.DEBUG)  # Handle DEBUG and above
    stdout_handler.addFilter(lambda record: record.levelno < logging.WARNING)  # Only log below WARNING
    stdout_handler.setFormatter(formatter)

    # Handler for stderr (WARNING and above levels)
    stderr_handler = logging.StreamHandler(sys.stderr)
    stderr_handler.setLevel(logging.WARNING)  # Handle WARNING and above
    stderr_handler.setFormatter(formatter)

    # Add handlers to the logger
    logger.addHandler(stdout_handler)
    logger.addHandler(stderr_handler)

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
    parser.add_argument('--sync-direction',
                        choices=[
                            'local_to_gdrive',
                            'gdrive_to_local',
                            'mirror',
                            'ask'
                        ],
                        default='mirror', help='options to use:'
                        'local_to_gdrive, gdrive_to_local, mirror, ask')
    parser.add_argument('--ignore', type=ignore_directory_parser, action='append',
                    help='ignore directories with the specified path and type.'
                    'Format: --ignore path=<path>,type=<type> '
                    '--ignore path=<path>,type=<type> ... .'
                    '<type>: single_file, all_files, folder'
                    '<path>: RELATIVE path INSIDE the syncing directory',
                    default=[])
    # Alternative mode. Have to use here 'optional' argument, --actions_json
    # though it's required in this mode
    # This mode ignores local_dir, sync_direction, --new, as it makes no sense
    parser.add_argument('--mode', type=str, choices=['partial_update'], help='Alternative mode, "partial_update"')
    parser.add_argument('--actions_json', type=str, help='Path to JSON file containing parameters (used with --mode partial_update)')

    args = parser.parse_args()

    # args = parser.parse_args([
    #     '/home/jastix/Documents/temp/1/remotevault/testVault',
    #     'testVault',
    #     '--mode',
    #     'partial_update',
    #     '--actions_json',
    #     '{"rename":{"321/9087/aaaaa":"321/9087/aaaaa1"}}'
    # ])
    # args = parser.parse_args([
    #     '/home/jastix/Documents/temp/TestVault',
    #     'TestVault',
    #     '--ignore',
    #     'path=.obsidian,type=folder',
    #     '--sync-direction',
    #     'mirror'
    # ])

    # Post-parsing validation
    if args.mode == 'partial_update':
        if not args.actions_json:
            logger.error("--actions_json must be provided when using --mode partial_update")
            exit()
        logger.debug(f'syncing with arguments: local dir - {args.local_path}, '
                     f'gdrive dir - {args.gdrive_dir}, '
                      '--mode partial_update, '
                     f'--actions_json - {args.actions_json}, ')
    else:
        logger.debug(f'syncing with arguments: local dir - {args.local_path}, '
                     f'gdrive dir - {args.gdrive_dir}, '
                     f'sync direction {args.sync_direction}' + 
                     (', create new dir' if args.new else '') +
                     (', ignored objects - ' + '; '.join([
                     f'path={x.rel_path},type={x.obj_type}' for x in args.ignore
                          ]) if args.ignore else ''))
    # exit if interactive mode and no local folder for syncing
    if not path.exists(args.local_path):
        logger.error('No local folder')
        sendmessage(f'{args.local_path} doesnt exist locally')
        exit()
    while retries:
        try:
            # it's a new mode so look a bit out of design
            if args.mode == 'partial_update':
                gdrive = GdriveSync(
                    **GOOGLE_LOGIN,
                    local_folder=args.local_path,
                    gdrive_folder=args.gdrive_dir
                )
                gdrive.sync_partial(args.actions_json)
                sendmessage('Partial sync was successfully applied', '10000')
                logger.info('All done well\n-----------------------')                
                # the work is done, don't allow retries
                break
            # standard mode
            else:
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
                # the work is done, don't allow retries
                break
        # if issues are related exactly to the network then wait and retry
        except (TimeoutError, TransportError, ServerNotFoundError, RefreshError):
            sendmessage(f'{args.gdrive_dir} wasnt synced, probably network issues, will retry', '10000')
            logger.error('Network error, retrying')
            sleep(120)
            retries -= 1
        # not a network related error
        except Exception as e:
            logger.error(f'Unexpected error, interrupted: {str(e)}')
            sendmessage(f'{args.gdrive_dir} wasnt synced, an error occured: {str(e)}')
            break
    else:
        logger.critical('Network error, out of retries')
        sendmessage(f'{args.gdrive_dir} wasnt synced, probably network issues, retries are over')
