#!/usr/bin/python3

#
#
# Hard link based incremental backup
#
# Copyright (c) 2020 Shigeru KANEMOTO
#
#

#XXX Recover files
#XXX Show files with error
#XXX Mode to stop an error found
#XXX Mode to make log file inside the set
#XXX Remove DB entries and the hash files for incomplete file.
#XXX Explicitly select the target set
#XXX Delete file entries in DB if not in the source.
#XXX リンク元ファイルが存在しない時どうするか
#XXX inprogressの途中のを再利用したい。
#XXX ブロックファイルの日時を記録しておき、変更無い事を確認すべき

import pathlib
import sqlite3
import hashlib
import sys
import os
import stat
import datetime

import argparse
import re

# Constants
INPROGRESS_DIRNAME = 'inprogress'
DATABASE_FILENAME = 'catalog.db'
COMMIT_INTERVAL_FILES = 100
BLOCK_SIZE = 2**27  # 128M

# Globals
destinationRoot = None          # '/mnt/e/backup'
destinationSet = None           # '/mnt/e/backup/inprogress'
destinationDatabase =  None     # sqlite3('/mnt/e/backup/inprogress/catalog.db')
referenceSet = None             # '/mnt/e/backup/20200603-1'
referenceDatabase = None        # sqlite3('/mnt/e/backup/20200603-1/catalog.db')
reExcludePattern = None         # Regular expresstion to find paths to exclude.
fileReadBuffer = None           # bytearray
optDryRun = False               # dry run
optShowBlockProgress = False    # show progress copying blocks
optShowFileProgress = False     # show unchanged files

# Statistics
catalogEntriesCounter = 0   # Number of total catalog entries inserted.
excludedPathsCounter = 0    # Number of excluded paths by '--exclude' command line option.
changedFilesCounter = 0     # Number of total files found.
unchangedFilesCounter = 0   # Number of unchanged files compared to the latest backup set.
directoriesCounter = 0      # Number of directories found.
symbolicLinksCounter = 0    # Number of symbolic links found.
processedBlocksCounter = 0  # Number of total blocks processed.
duplicateBlocksCounter = 0  # Number of duplicate blocks found in the same backup set.
linkedBlocksCounter = 0     # Number of blocks linked to other backup set in the same destination root.
createdBlocksCounter = 0    # Number of created blocks.
linkedDiskBlocks = 0        # Number of 1k disk blocks linked.
createdDiskBlocks = 0       # Number of 1k disk blocks created.

#
# Utilities
#

def last_insert_rowid():
    cur = destinationDatabase.execute('select last_insert_rowid()')
    id = cur.fetchone()[0]
    cur.close()
    return id

def first(iterable):
    try:
        return next(iterable)
    except StopIteration:
        return None

def encode64(value):
  value &= (1<<64)-1
  if (value & (1<<63)) != 0:
    value -= 1<<64
  return value

def decode64(value):
  if value < 0:
    value += 1<<64
  return value

#
# Database Operations
#

def insertFileEntry(sourceId, relativePath, filetype, st, link=None):
    # sourceId: source root directory id
    # relativePath: pathlib.PurePath object relative to the source root directory
    # filetype: F for file, N for new file, L for symlink, D for directory
    # st: os.stat object
    # link: symlink target or None
    try:
        destinationDatabase.execute(
            'insert or replace into '
                'file(id, source, path, type, mode, uid, gid, lastmod, size, link) '
                'values('
                    '(select id from file where source = :source and path = :path), '
                    ':source, :path, :type, :mode, :uid, :gid, :lastmod, :size, :link'
                ')',
            {
                'source': sourceId,
                'path': str(relativePath),
                'type': filetype,
                'mode': '{:o}'.format(st.st_mode),
                'uid': st.st_uid,
                'gid': st.st_gid,
                'lastmod': encode64(st.st_mtime_ns),
                'size': st.st_size,
                'link': link
            }
        )
    except OverflowError as e:
        raise e

    global catalogEntriesCounter
    catalogEntriesCounter += 1
    if catalogEntriesCounter % COMMIT_INTERVAL_FILES == 0:
        destinationDatabase.commit()

def deleteBlockEntriesForFile(file):
    destinationDatabase.execute('delete from block where file = ?', (file,))

def insertBlockEntry(file, offset, size, hash):
    destinationDatabase.execute(
        'insert into '
            'block(file, offset, size, hash) '
            'values(:file, :offset, :size, :hash)',
        {
            'file': file,
            'offset': offset,
            'size': size,
            'hash': hash
        }
    )

#
# Block Operations
#

def linkOrCreateBlock(hash, view):
    global processedBlocksCounter
    processedBlocksCounter += 1

    # Make the block file name and make the parent directory
    blockFile = destinationSet / hash[:2]
    if not optDryRun and not blockFile.is_dir():  # raise
        blockFile.mkdir()   # raise
    blockFile /= hash[2:]

    # Skip if already exists in the same destination backup set
    if not optDryRun and blockFile.is_file() and blockFile.stat().st_size == len(view):
        global duplicateBlocksCounter
        duplicateBlocksCounter += 1
        return False

    # Link if already exists in any of other backup sets
    ref = first(destinationRoot.glob('*/{}/{}'.format(hash[:2], hash[2:])))
    if ref and ref.is_file() and ref.stat().st_size == len(view):
        if not optDryRun:
            ref.link_to(blockFile)
        global linkedBlocksCounter
        linkedBlocksCounter += 1
        return False

    # Dump the given memory into the file
    if not optDryRun:
        fd = os.open(str(blockFile), os.O_WRONLY|os.O_CREAT|os.O_TRUNC) # raise
        n = os.writev(fd, [view])   # raise OSError
        os.close(fd)
        if n != len(view):
            raise RuntimeError

    global createdBlocksCounter
    createdBlocksCounter += 1
    return True

def linkReferenceBlock(hash):
    # Make the block file name and make the parent directory
    blockFile = destinationSet / hash[:2]
    if not blockFile.is_dir():  # raise
        blockFile.mkdir()   # raise
    blockFile /= hash[2:]

    # Make a hard link from the reference to the destination
    try:
        (referenceSet / hash[:2] / hash[2:]).link_to(destinationSet / hash[:2] / hash[2:])
    except FileExistsError:
        return True
    except FileNotFoundError:
        #XXX リンク元ファイルが存在しない時どうするか
        print('hash file not found in reference', hash)
        return False
    return True

#
# Backup Files, Directories and Symlinks
#

def backupFile(sourceId, refSourceId, relativePath, path):
    # Insert the catalog entry
    st = path.stat()
    insertFileEntry(sourceId, relativePath, 'F', st)
    fileId = last_insert_rowid()    # Get the file.id just inserted

    #XXX 途中のを再利用したい。
    deleteBlockEntriesForFile(fileId)

    # Check if changed
    global linkedDiskBlocks
    while refSourceId:
        cur = referenceDatabase.execute(
            "select id, lastmod, size from file "
            "where source = :source and path = :path and type = 'F'",
            {'source': refSourceId, 'path': str(relativePath)}
        )
        row = cur.fetchone()
        cur.close()
        if not row:
            # No entries found in the reference set.
            break
        if row['lastmod'] != encode64(st.st_mtime_ns):
            # mtime changed
            break
        if row['size'] != st.st_size:
            # size changed
            break

        cur = referenceDatabase.execute('select * from block where file = :file', {'file': row['id']})
        for row in cur:
            hash = row['hash']
            if not optDryRun:
                if not linkReferenceBlock(hash):
                    print('block file disappeared for', relativePath, hash)    #XXX
            linkedDiskBlocks += (row['size'] + 1023) // 1024
            insertBlockEntry(fileId, row['offset'], row['size'], hash)

        if optShowFileProgress:
            print('-/-/U {}'.format(relativePath))
        global unchangedFilesCounter
        unchangedFilesCounter += 1
        return  # This 'while' is not intended as a loop

    # Open the source file and split into block files
    global changedFilesCounter
    changedFilesCounter += 1
    try:
        fd = os.open(str(path), os.O_RDONLY)    # raise FileNotFoundError, O_BINARY?
    except PermissionError:
        #XXX Log
        return
    except OSError:
        #XXX Log other OS error
        return

    global createdDiskBlocks
    total = (st.st_size + BLOCK_SIZE - 1) // BLOCK_SIZE
    checked = 0
    created = 0
    offset = 0
    while True:
        if optShowBlockProgress:
            print('{:d}/{:d}/{:d} {}'.format(created, checked, total, relativePath), end='\r')
        try:
            n = os.readv(fd, [fileReadBuffer])
        except OSError:
            # File opened, but could not be read.
            # Mandatory Lock file etc.
            #XXX Log
            break
        if n == 0:
            # EOF
            break
        view = memoryview(fileReadBuffer)
        view = view[:n]
        hash = hashlib.sha1(view).hexdigest()
        if linkOrCreateBlock(hash, view):
            created += 1
            createdDiskBlocks += (n + 1023) // 1024
        else:
            linkedDiskBlocks += (n + 1023) // 1024
        insertBlockEntry(fileId, offset, n, hash)
        offset += n
        checked += 1

    os.close(fd)
    print('{:d}/{:d}/{:d} {}'.format(created, checked, total, relativePath))

def backupSymlink(sourceId, relativePath, path):
    link = os.readlink(path)    # pathlib.Path.readlink() first appears in Python 3.9
    insertFileEntry(sourceId, relativePath, 'S', path.lstat(), link)

    if optShowFileProgress:
        print('-/-/S {}'.format(relativePath))
    global symbolicLinksCounter
    symbolicLinksCounter += 1

def backupDirectory(sourceId, refSourceId, relativePath, path):
    # Do not walk down into the backup target directory
    #XXX statを減らしたい
    if destinationRoot.exists() and destinationRoot.samefile(path):
        return
    if destinationSet.exists() and destinationSet.samefile(path):
        return

    insertFileEntry(sourceId, relativePath, 'D', path.stat())
    if optShowFileProgress:
        print('-/-/D {}'.format(relativePath))
    global directoriesCounter
    directoriesCounter += 1

    for child in path.iterdir():
        r = relativePath / child.name
        # Exclude
        if reExcludePattern and reExcludePattern.search(str(r)):
            if optShowFileProgress:
                print('-/-/X {}'.format(relativePath))
            global excludedPathsCounter
            excludedPathsCounter += 1
            continue

        try:
            st = child.stat()
            if stat.S_ISLNK(st.st_mode):
                backupSymlink(sourceId, r, child)
            elif stat.S_ISDIR(st.st_mode):
                backupDirectory(sourceId, refSourceId, r, child)
            elif stat.S_ISREG(st.st_mode):
                backupFile(sourceId, refSourceId, r, child)
            else:
                # Special files will be ignored
                #XXX Log file path
                pass
        except PermissionError:
            #XXX Log file path
            continue

#
# Backup Given Directories
#

def backup(dirs):
    global destinationSet
    global destinationDatabase
    global referenceDatabase

    destinationSet = destinationRoot / INPROGRESS_DIRNAME
    if optDryRun:
        destinationDatabase = sqlite3.connect(':memory:')
    else:
        # Create the destination set and the database
        destinationSet.mkdir(parents=True, exist_ok=True)   # raise PermissionError
        destinationDatabase = sqlite3.connect(str(destinationSet / DATABASE_FILENAME))    # raise PermissionError

    # Create the tables
    destinationDatabase.row_factory = sqlite3.Row
    destinationDatabase.execute(
        'create table if not exists '
            'source('
                'id integer primary key, '
                'path text unique not null'
            ')'
    )
    destinationDatabase.execute(
        'create table if not exists '
            'file('
                'id integer primary key, '  # referred from block
                'source integer not null, ' # source dir number from 0
                'path text not null, '      # file path relative to the src
                'type text, '               # F for file, N for new file, L for symlink, D for directory
                'mode text, '               # octal mode in text
                'uid integer, '             # uid
                'gid integer, '             # gid
                'lastmod integer, '         # mtime in ns
                'size integer, '            # file size
                'link text, '               # symlink destination
                'unique(source, path)'
            ')'
    )
    destinationDatabase.execute(
        'create table if not exists '
            'block('
                'file integer not null, '   # file.id
                'offset integer not null, ' # byte offset of this block
                'size integer not null, '   # size of this block
                'hash text not null, '      # hash
                'unique(file, offset, size)'
            ')'
    )

    if referenceSet:
        referenceDatabase = sqlite3.connect('file:{}?mode=ro'.format(str(referenceSet / DATABASE_FILENAME)), uri=True)  # raise PermissionError
        referenceDatabase.row_factory = sqlite3.Row

    # Backup the directories
    for path in dirs:
        # Absolute path
        path = pathlib.Path(path).resolve()

        # Find or Add a source id for this path
        destinationDatabase.execute('insert or replace into source(id, path) values((select id from source where path = :path), :path)', {'path': str(path)})
        sourceId = last_insert_rowid()

        # Find a source id for reference
        refSourceId = 0
        if referenceDatabase:
            cur = referenceDatabase.execute('select id from source where path = :path', {'path': str(path)})
            row = cur.fetchone()
            cur.close()
            if row:
                refSourceId = row[0]

        # Backup
        if optDryRun:
            print('# Dry Run')
        print('# Backup', path)
        backupDirectory(sourceId, refSourceId, pathlib.PurePath('/'), path)

    # Close the database
    destinationDatabase.commit()
    destinationDatabase.close()
    if referenceDatabase:
        referenceDatabase.close()

#
# Application
#

def initialize():
    # Initialize
    global destinationRoot
    if not destinationRoot.is_dir():    # raise
        raise RuntimeError

    global fileReadBuffer
    fileReadBuffer = bytearray(BLOCK_SIZE)

def selectReferenceBackupSet():
    def sortkey(name):
        n = name.name.split('-')
        if len(n) == 1:
            return (n[0], 0)
        return (n[0], int(n[1]))

    names = [s for s in pathlib.Path(destinationRoot).glob('[0-9]*') if s.is_dir()]
    names.sort(key=sortkey)
    if len(names) > 0:
        global referenceSet
        referenceSet = names[-1]

def renameToDateString():
    datestring = datetime.date.today().strftime('%Y%m%d')
    serial = 0
    d = destinationRoot / datestring
    while d.exists():
        serial += 1
        d = destinationRoot / ('{:s}-{:d}'.format(datestring, serial))

    global destinationSet
    destinationSet = d if optDryRun else destinationSet.rename(d)

def showStatistics():
    if optDryRun:
        print('# Dry Run')
    print('# Statistics')
    print('Created Set: {:s}'.format(str(destinationSet)))
    print('Reference Set: {:s}'.format(str(referenceSet) or 'None'))
    print('eXcluded Paths: {:d}'.format(excludedPathsCounter))
    print('Catalog Entries: {:d}'.format(catalogEntriesCounter))
    print('  Changed Files: {:d}'.format(changedFilesCounter))
    print('  Unchanged Files: {:d}'.format(unchangedFilesCounter))
    print('  Directories: {:d}'.format(directoriesCounter))
    print('  Symbolic Links: {:d}'.format(symbolicLinksCounter))
    print('Blocks: {:d}'.format(processedBlocksCounter))
    print('  Duplicate: {:d}'.format(duplicateBlocksCounter))
    print('  Linked to Other Set: {:d}'.format(linkedBlocksCounter))
    print('  Created: {:d}'.format(createdBlocksCounter))
    print('Disk Blocks: {:d} k'.format(createdDiskBlocks + linkedDiskBlocks))
    print('  Linked Disk Blocks: {:d} k'.format(linkedDiskBlocks))
    print('  Created Disk Blocks: {:d} k'.format(createdDiskBlocks))

def main():
    # Parse the arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('-d', '--destination', type=pathlib.Path, required=True, help='backup data store directory')
    parser.add_argument('--exclude', action='append', type=str, help='exclude path or name')
    parser.add_argument('-n', '--dry-run', action='store_true', help='dry run')
    parser.add_argument('--show-block-progress', action='store_true', help='show block progress')
    parser.add_argument('--show-file-progress', action='store_true', help='show file progress')
    parser.add_argument('source', type=str, nargs='+')
    args = parser.parse_args()
    global destinationRoot
    destinationRoot = args.destination

    def makeExcludePattern(name):
        pattern = r'\*\*|\*|\?|\.|\^|\$|\+|\{|\\|\[|\||\('
        def repl(m):
            m = m.group(0)
            if m == '**':
                return '.*'
            if m == '*':
                return '[^/]*'
            if m == '?':
                return '[^/]'
            if m == '[':
                return '['
            return '\\' + m
        if '*' in name or '?' in name or '[' in name:
            # Make re to match wildcard
            name = re.sub(pattern, repl, name)
        if name.startswith('/'):
            return '^' + name + '$'
        else:
            return '/' + name + '$'

    if args.exclude:
        global reExcludePattern
        reExcludePattern = re.compile('|'.join(makeExcludePattern(name) for name in args.exclude))

    global optDryRun
    optDryRun = args.dry_run
    global optShowBlockProgress
    optShowBlockProgress = args.show_block_progress
    global optShowFileProgress
    optShowFileProgress = args.show_file_progress

    # Backup given source directories
    initialize()
    selectReferenceBackupSet()
    backup(args.source)
    renameToDateString()
    showStatistics()

if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        destinationDatabase.commit()
        sys.exit(130)   # 128 + SIGINT
