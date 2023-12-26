# This scrypt is for syncing a local directory with a directory on
# Google Drive. Takes two arguments: the local directory absolute path
# and the google drive os-like path, i.e. a path relative to the
# Google Drive root <foldername>/<innerfolder>/...
# With flag -n a new gdrive directory will be created instead of
# searching an existing one


import subprocess
from os import path, listdir
from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google.auth.exceptions import TransportError, RefreshError
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from googleapiclient.http import MediaFileUpload
from httplib2 import ServerNotFoundError
from datetime import datetime
from concurrent.futures import TimeoutError
from time import sleep, time
from argparse import ArgumentParser

DEBUG = False

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

class Onetier:
    """this class is meant to store lists of filenames and
    directory names in some direcorty and parents as a relative path
    """
    def __init__(self, parents: str='', gparent: str|None = None) -> None:
        """files and dirs are initialized as empty lists, so
        elements can be added there in a loop. tier is the amount
        of parents, i.e. the amount of directories in relative path

        Args:
            parents (str, optional): just additional information.
                        relative path on gdrive
            gparent (str|None, optional): for gdrive items only,
                        because they have and relative path which is
                        for a user and parent folder id, which is for API
        """
        self.files = []
        self.dirs = []
        self.parents = parents
        self.tier = 0 if not parents else len(parents.split('/'))
        self.gparent = gparent
    
def iterate_dircontent(dir) -> list[Onetier]:
    """returns Onetier object for each directory in a tree.
    For files - adds up a file modification type in a tuple
    (filename, mtime).

    Args:
        dir (_type_): an absolute path to a root directory
                    for which this function returns lists of
                    contents

    Returns:
        list[Onetier]: Onetier for each directory, the root 'dir'
                    including
    """
    if DEBUG:
        print('Creating local structure')
    dirs_to_visit = [] # dirs to make Onetier for each
    result = [] # total result
    def one_tier_files(parents: str) -> None:
        """gets non resursive contents of one directory, stores
        it into a Onetier object, adds the object to totale result,
        adds directories to dirs_to_visit if there are any

        Args:
            parents (str): relative 'shift' inside the root dir

        Returns: nothing, because modifies variables of parent func
        """
        for_return = Onetier(parents=parents)
        current_dir = path.join(dir, parents) # get abs path
        # loop over all items in a directory
        for item in listdir(current_dir):
            item_full = path.join(current_dir, item) # get abs path of an item
            # skip links. They are dangerous and not needed on gdrive
            if path.islink(item_full):
                continue
            # add files as tuples with their modification times
            if path.isfile(item_full):
                for_return.files.append((item, path.getmtime(item_full)))
                continue
            # add dir to the result and to the list of dirs to visit
            if path.isdir(item_full):
                for_return.dirs.append(item)
                dirs_to_visit.append((parents, item))
        result.append(for_return)
    
    # call for the root dir
    one_tier_files('')
    # loop over all other dirs with any nesting inside the root dir
    while dirs_to_visit:
        one_tier_files(path.join(*dirs_to_visit.pop(0)))
    if DEBUG:
        print('Created local structure')
    return result

class GdriveSync:
    def __init__(
        self,
        client_secrets_file: str,
        token_file: str,
        scopes: list[str],
        folder: str='',
        create_folder: bool=False
    ) -> None:
        self.client_secrets_file = client_secrets_file
        self.token_file = token_file
        self.scopes = scopes
        self.folder = folder.strip('/')
        self.create_folder = create_folder
        self.creds = None
        self.service = None

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

    def create_gdrive_folder(self, folder_name: str, parent_folder_id: str|None=None) -> str:
        """creates a folder on gdrive with given name and parent id

        Args:
            folder_name (str): a name of a folder to create
            parent_folder_id (str | None, optional): parent folder id.

        Returns:
            str: newly created forlder id
        """
        if DEBUG:
            print(f'Creating folder {folder_name}')
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
    
    def _get_folder_parent(self, item_id: str) -> str:
        """requests an id if a parent folder to item 'item_id'. Item can
        be either a file or a folder.

        Args:
            item_id (str): an id of an item, which parent we want to know

        Returns:
            str: an id of the item't parent
        """
        if DEBUG:
            print(f'Getting folder parent of {item_id}')
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
        if DEBUG:
            print(f'Searching sync directory {self.folder} on gdrive')
        self.make_creds() # always check
        dir_exists = True # init with assumption we'll find the dir
        # gdrive doesn't support os-like paths, so we have to check
        # the existence of every item in the path chain
        folder_chain = self.folder.split('/')
        parent_folder_id = 'root' # search start point
        while folder_chain:
            folder_name = folder_chain.pop(0) # get the topmost element
            # query to request a folder with required name and parent
            query = f"'{parent_folder_id}' in parents and name='{folder_name}' and trashed=false and mimeType = 'application/vnd.google-apps.folder'"
            results = self.service.files().list(q=query, fields='files(id)').execute().get('files', [])
            # if found, then we can go deeper by the chain
            if results:
                # two folders can't have the same name, so there always
                # be not more than one element in the returned list
                parent_folder_id = results[0]['id']
            # if not found, then create the rest of the absent chain
            else:
                dir_exists = False
                # put back the removed above item, since we didn't find it
                folder_chain.insert(0, folder_name)
                # simply create all absent
                for item in folder_chain:
                    parent_folder_id = self.create_gdrive_folder(item, parent_folder_id)
                break
        if DEBUG:
            print(f'Found folder {self.folder} on gdrive')
        return (dir_exists, parent_folder_id)

    def _iterate_gdrive(self, folder_id: str) -> list[Onetier]:
        """Takes folder_id as a starting point and returns the
        gdrive structure, consisting of Onetier objects with the
        gparent field, which is the actual id of the folder

        Args:
            folder_id (str): id of the folder on gdrive to make
                        the structure of

        Returns:
            list[Onetier]: a list of contents of every folder
        """
        if DEBUG:
            print('Start creating gdrive structure')
        self.make_creds() # always check
        parent_folder_id = folder_id # starting point
        parent_name = '' # relative root for os-like path
        dirs_to_visit = [] # nested dirs
        result = [] # tital result
        def one_tier_files() -> None:
            """Processes one folder, creating the Onetier object.
            Doesn't take or return anything because operates with
            it's parent function variables
            """
            for_return = Onetier(parents=parent_name, gparent=parent_folder_id) # init new
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
                else:
                    for_return.files.append((item['name'], item['id'], datetime.fromisoformat(item['modifiedTime']).timestamp()))
            result.append(for_return) # add new Onetier to the result
        # call for the root dir
        one_tier_files()
        # loop over all other dirs with any nesting inside the root dir
        while dirs_to_visit:
            dir_name, parent_folder_id, tmp_parent = dirs_to_visit.pop(0)
            parent_name = path.join(tmp_parent, dir_name)
            one_tier_files()
        if DEBUG:
            print('Finished creating gdrive structure')
        return result

    def delete_file_or_folder(self, file_id: str) -> None:
        """Deletes an object with said id on gdrive

        Args:
            file_id (str): id of an object to delete
        """
        if DEBUG:
            print(f'Deleting {file_id}')
        self.make_creds()
        try:
            self.service.files().delete(fileId=file_id).execute()
        except HttpError:
            print(f'{file_id} отсутствует')

    def batch_delete_files(self, files_to_delete: list) -> None:
        """Deletes all objects in the list in one request

        Args:
            files_to_delete (list): a list of ids of objects
                        to delete
        """
        if DEBUG:
            print(f'Batch deleting {files_to_delete}')
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
            local_path (str): the path to the file in fs
            file_id (str): id of a file on gdrive
        """
        if DEBUG:
            print(f'Updating file {path.basename(local_path)}')
        self.make_creds()
        media = MediaFileUpload(local_path, resumable=True)
        self.service.files().update(fileId=file_id, media_body=media).execute()


    def upload_file(self, file_to_upload: str, parent: str='root') -> None:
        """Uploads a new file to gdrive. If a file with such name
        exists, it will be uploaded as a separate file regardless

        Args:
            file_to_upload (str): the path to the file in fs
            parent (str, optional): folder id on gdrive where
                        the file will be located
        """
        if DEBUG:
            print(f'Uploading file {path.basename(file_to_upload)}')
        self.make_creds()
        file_metadata = {
            'name': path.basename(file_to_upload),
            'parents': [parent]
        }
        media = MediaFileUpload(file_to_upload, resumable=True)
        self.service.files().create(body=file_metadata, media_body=media).execute()

    def _compare_flat(self, local: Onetier, gdrive: Onetier, local_dir: str) -> list:
        """Compares two Onetier objects, and makes all necessary changes
        to reflect local directory to gdrive directory

        Args:
            local (Onetier): local directory
            gdrive (Onetier): gdrive directory
            local_dir (str): absolute path too the local directory in fs

        Returns:
            list: a list of Onetier objects, i.e. new gdrive folders
                        which were created in a process of reflecting
                        and should be added to the gdrive structure
        """
        if DEBUG:
            print(f'Comparing tier {local.parents}')
        files_to_delete = [] # for bacth delete
        new_struct_items = [] # new folders created, for returning
        # go over all files in a local dir
        while local.files:
            local_file, local_mtime = local.files.pop()
            # go over all files in a gdrive dir
            for item in gdrive.files:
                g_name, g_id, g_mtime = item
                # if the same file name found
                if g_name == local_file:
                    # check if the local file is newer
                    if local_mtime > g_mtime:
                        # if so - update gdrive file
                        self.update_file(path.join(path.join(local_dir, local.parents), local_file), g_id)
                    # remove the processed file from gdrive list
                    gdrive.files.remove(item)
                    break
            # if a file not found, means it's absent on gdrive, upload it
            else:
                self.upload_file(path.join(path.join(local_dir, local.parents), local_file), gdrive.gparent)
        # if anything remins in the list of gdrive files, means these files
        # are absent locally and should be deleted
        for item in gdrive.files:
            files_to_delete.append(item[1])
        # loop over local dirs
        while local.dirs:
            local_dir = local.dirs.pop()
            # loop over gdrive dirs
            for item in gdrive.dirs:
                g_name, g_id = item
                # if directory exists on gdrive
                if g_name == local_dir:
                    # remove a processed one from the list
                    gdrive.dirs.remove(item)
                    break
            # if no such dir, then create it and create a corresponding empty Onetier object
            else:
                new_folder = self.create_gdrive_folder(local_dir, gdrive.gparent)
                new_struct_items.append(Onetier(parents=path.join(local.parents, local_dir), gparent=new_folder))
        # remove the remaining on gdrive dirs, which were not found locally
        for item in gdrive.dirs:
            files_to_delete.append(item[1])
        # delete all objects marked for this
        self.batch_delete_files(files_to_delete)
        if DEBUG:
            print(f'Finished to compare tier {local.parents}')
        return new_struct_items        

    def sync(self, local_dir: str, local_struct: list[Onetier]) -> None:
        """Syncs the local and gdrive directory

        Args:
            local_dir (str): absolute path to the local directory
            local_struct (list[Onetier]): structure, made of Onetier
                        objects for this local directory
        """
        if DEBUG:
            print('Start syncing')
        exists, root_gdir = self._search_sync_dir()
        # a flag to make a new folder on gdrive instead of
        # searching the existing one to sync with
        if self.create_folder and exists:
            parent_dir = self._get_folder_parent(root_gdir)
            new_folder_name = f'{self.folder.split("/")[-1]}_{str(int(time()))}'
            root_gdir = self.create_gdrive_folder(new_folder_name, parent_dir)
        # get the gdrive structure
        gdrive_struct = self._iterate_gdrive(root_gdir)
        # split the local structure by it's tiers, where tier -
        # is the level of nesting
        tiers = {}
        for item in local_struct:
            if item.tier in tiers.keys():
                tiers[item.tier].append(item)
            else:
                tiers[item.tier] = [item]
        # go from the top (root) tier to the bottom
        # it will help to cut off unnecessary brancehs
        for item in sorted(tiers.keys()): # loop over tiers starting on top
            for elem in tiers[item]: # loop over every dir on this tier
                for g_item in gdrive_struct: # loop gdrive folders
                    # when gdrive folder will be found (and it will be found
                    # if no errors happened, because any absent folder will be created
                    # with the processing of the previous tier)
                    if elem.parents == g_item.parents:
                        # reflect local structure to the grdive structure
                        gdrive_struct.extend(self._compare_flat(elem, g_item, local_dir))
                        break
        if DEBUG:
            print(f'Finish syncing')

def sendmessage(message: str='', timeout: str='0') -> None:
    """Sends a message to notification daemon in a separate process.
    urgency=critical makes a message stay until closed manually,
    for other message types types don't forget timeout"""

    icon = '/home/jastix/Documents/icons/gdrive_256.png'
    subprocess.Popen(['notify-send', '-i', icon, '-t', timeout, 'gdrive sync', message])


if __name__ == '__main__':
    retries = 3 # three attempts to sync, in case of network issues
    parser = ArgumentParser()
    parser.add_argument('local_path')
    parser.add_argument('gdrive_dir')
    parser.add_argument("-n", "--new", action="store_true")
    args = parser.parse_args()
    local_dir = args.local_path
    gdrive_dir_name = args.gdrive_dir
    if path.exists(local_dir):
        local_struct = iterate_dircontent(local_dir)
        while retries:
            try:
                gdrive = GdriveSync(**GOOGLE_LOGIN, folder=gdrive_dir_name, create_folder=args.new)
                gdrive.sync(local_dir, local_struct)
                sendmessage(f'{gdrive_dir_name} successfully synced', '10000')
                if DEBUG:
                    print('All done well')
                break # the work is done
            # if issues are related exactly to the network then wait and retry
            except (TimeoutError, TransportError, ServerNotFoundError, RefreshError):
                sendmessage(f'{gdrive_dir_name} wasnt synced, probably network issues, will retry', '10000')
                if DEBUG:
                    print('Network error, retrying')
                sleep(120)
                retries -= 1
            except Exception as e:
                if DEBUG:
                    print('Unexpected error, interrupted')
                sendmessage(f'{gdrive_dir_name} wasnt synced, an error occured: {str(e)}')
                break
        else:
            if DEBUG:
                print('Network error, out of retries')
            sendmessage(f'{gdrive_dir_name} wasnt synced, probably network issues, retries are over')
    else:
        if DEBUG:
            print('No local folder')
        sendmessage(f'{local_dir} doesnt exist locally')
