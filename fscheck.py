#!/usr/bin/python
"""
fscheck
a module for Python

ABOUT THIS PROGRAM

A consistency check for checking what files were made unavailable by bad
sectors.

Say you have a disk with bad sectors, you copy the partitions off it using
gddrescue. You don't know what files were broken or made unavailable by
directory inodes becoming corrupt. This program scans the directories, starting
with an initial set (for example the root directory or a list of specific
directories) and recurs into them, checking for errors. It does not list
erroneous files.

This program is used as a Python module which you import into the interpreter.
You instantiate the FSCheck class and feed it a gddrescue log. It uses debugfs
(the ext3 filesystem debugger interpreter, not the kernel debugging tool)
through a fairly finicky but surprisingly solid pexpect integration. It is very
slow because it needs to save out a file for every command! There is no python
interface for any debugfs-like functionality, alas.

It's fairly conservative with resources, even with 30k files scanned the Python
interpreter running it takes no more than 50 megabytes memory.

LICENSE

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

class BadBlocks(object):
    """ Contains the bad block number description as well as a host of
        utility functions.
        """
    def concatenate(self, lines):
        if any([line[2] not in ['-', '/'] for line in lines]):
            raise ValueError("The reports to join should be bad blocks only.")
        for prev, next in zip(lines, lines[1:]):
            if next[0] != prev[0] + prev[1] + 1:
                raise ValueError("The reports must be contiguous.")
        out = (lines[0][0], lines[-1][0] + lines[-1][1] - lines[0][0], '-')
        return out

    lines = []
    def add(self, line):
        self.lines.append(line)

    def __init__(self, gddrescuelog):
        """ The constructor. Pass a gddrescue log file handle in order to
            parse the data there into a usable BadBlocks.
            """
        if not gddrescuelog:
            raise ValueError("Invalid gddrescue log!")
        line_acc = []
        for l in gddrescuelog.readlines()[4:]:
            raw_line = l.rstrip().split('  ')
            line = (
                int(raw_line[0], 16),
                int(raw_line[1], 16) - 1,
                raw_line[2]
                )
            if line[2] == '+':
                if line_acc:
                    self.add(self.concatenate(line_acc))
                self.add(line)
                line_acc = []
            else:
                line_acc.append(line)

    def block_ok(self, block_num):
        """ Checks the block - whether it is good or bad.
            Returns True for good blocks, False for bad blocks."""
        for i in range(len(self.lines)):
            if self.lines[i][0] > block_num:
                if i == 0:
                    raise Exception(
                        'The reports describe blocks that have'
                        'higher numbers than the block being tested.'
                        )
                return {'+': True, '-': False}[self.lines[i-1][2]]

def rmrf(path):
    """ Kinda like rm -rf. """
    import shutil, errno, os
    try:
        shutil.rmtree(path)
    except OSError as e:
        if errno.ENOTDIR == e.errno:
            os.unlink(path)
        elif errno.ENOENT != e.errno:
            raise

CONTINUE = 0
SUSPEND = 1

import tempfile, os, re, sys, pexpect, time
class FSCheck(object):
    """ This class contains info about all the files and also contains the
        test and traversal logic.
        """
    def wait_prompt_unsafe(self):
        self.debugfs.expect('debugfs:  ')

    def wait_prompt(self):
        """ Wait for the debugfs prompt. """
        try:
            self.wait_prompt_unsafe()
        except pexpect.EOF:
            self.setup_debugfs_on_error()

    log = sys.stderr
    unnamed_files = []
    deleted_files = []
    dir_ = None
    pexpect_retries = 0
    pexpect_retries_unique = 0
    pexpect_restarts = 0

    def setup_debugfs_on_error(self):
        """ Use this to restart debugfs when an error happens. Do not use
            during normal operation.
            """
        self.log.write('Restarting debugfs because of an error.\n')
        self.setup_debugfs()
        self.pexpect_restarts += 1

    def setup_debugfs(self):
        """ Sets up a fresh instance of debugfs and the communication dir. """
        self.debugfs = pexpect.spawn('debugfs %s' % self.partition)
        self.wait_prompt_unsafe()
        if self.dir_:
            rmrf(self.dir_)
        self.dir_ = tempfile.mkdtemp()

    def __init__(self, bad_blocks, partition):
        import subprocess
        if subprocess.call(['test', '-b', partition]) is not 0:
            raise ValueError(
                'The path "%s" is not a block special device.' % partition
                )
        self.partition = partition
        self.setup_debugfs()
        self.bad_blocks = bad_blocks

    def sleep(self, tries):
        """ Sleeps for a certain amount of time so that pexpect can catch up.
            """
        if tries > 0:
            period = 0.05 * (tries ** 2)
#             time.sleep(period)
            try:
                self.debugfs.expect(pexpect.EOF, timeout=period)
            except pexpect.TIMEOUT:
                pass

    def cmd(self, cmd):
        """ Runs a command which results in the use of a pager, and returns
            the output as a string.
            """
        file_ = os.path.join(self.dir_, 'out')
        tries = 0
        if os.path.exists(file_):
            rmrf(file_)
        while True:
            try:
                self.debugfs.sendline(cmd)
                self.sleep(tries)
                self.debugfs.send('s')
                self.sleep(tries)
                self.debugfs.sendline(file_)
                self.sleep(tries)
                self.debugfs.sendline('q')
                self.wait_prompt()

                if os.path.exists(file_):
                    out = file(file_).read()
                    rmrf(file_)
                    return out
            except pexpect.EOF:
                # Sometimes it just dies because the q was entered in the
                # interactive context and not in the context of less.
                self.setup_debugfs_on_error()
            tries += 1
            limit = 8

            self.pexpect_retries += 1
            if tries == 1:
                self.pexpect_retries_unique += 1

            if tries > limit:
                self.log.write(
                    'Aborting after %d tries. Please input path to ' % limit \
                    + 'file in order to manually override. The command is:\n' \
                    + '%s\n' % cmd
                    )
                while True:
                    path = raw_input('> ')
                    if os.path.exists(path):
                        self.setup_debugfs_on_error()
                        return file(path).read()
                    self.log.write(
                        'Could not find path %s. Please enter a path.\n'
                        )

            if tries > 2:
                self.log.write(
                    'Could not get output data for command:\n%s\n' % cmd \
                    + 'Retrying, attempt #%d\n' % tries
                    )
                self.log.write('Temporary directory:\n%s\nExists: %s\n' % (
                    self.dir_,
                    os.path.exists(self.dir_),
                    ))
            if tries > 6:
                self.log.write('Printing more debug info because there were ' \
                    + 'too many retries.\n'
                    )
                try:
                    self.debugfs.expect(pexpect.EOF, timeout=30)
                except pexpect.TIMEOUT:
                    pass
                self.log.write('Before:\n%s\nAfter:\n%s\n' % (
                    self.debugfs.before,
                    self.debugfs.after
                    ))
            if tries > 4:
                self.setup_debugfs_on_error()

    def _old_ls(self, path):
        """ Returns the filenames of the files inside a directory. """
        info = self.cmd('ls %s' % path).strip()
        files = []
        if info:
            for line in info.split('\n'):
                for file_ in line.split('    '):
                    file_info = file_.split('  ')[1].split(' ')
                    if len(file_info) == 1:
                        pass
                    elif len(file_info) == 2:
                        files.append(file_info[1])
                    else:
                        raise Exception(
                            'Invalid file identifier. %s for path %s' % (
                                repr(file_),
                                path,
                                ))
        return files

    def ls(self, path):
        """ Returns the filenames of the files inside a directory. """
        info = self.cmd('ls -p "%s"' % path).strip()
        files = []
        if info:
            for line in info.split('\n'):
                file_ = None
                try:
                    first_split = line.split('/', 5)
                    inode = int(first_split[1])
                    file_ = first_split[-1].rsplit('/', 2)[0]
                    error = False
                    if file_ == '':
                        self.log.write(
                            'Found file without name:\n%s\n' % line \
                            + 'while listing the path:\n%s\n' % path \
                            + 'inode number: %d\n'
                            )
                        self.unnamed_files.append((path, line))
                        error = True
                    if inode == 0:
                        self.deleted_files.append((path, line))
                        error = True
                    if error:
                        continue
                    if '/' in file_:
                        file_ = '\/'.join(file_.split('/'))
                    files.append(file_)
                except IndexError:
                    err = 'Invalid identifier for path %s:\n' % path \
                        + 'Identifier:\n%s\nFile_:\n%s\n' % line, repr(file_)
                    self.log.write(err)
                    raise Exception(err)
        return files

    def get_path_info(self, path):
        """ Gets the info about a file:
            {
                type: the type of the file
                blocks: list of block numbers
                files: if a directory, this lists the files inside it.
                }
            """
        info = self.cmd('stat "%s"' % path)
        lines = info.split('\n')
        type_matches = re.search('Type: (.*)Mode:', lines[0])
        if not type_matches:
            raise Exception(
                'The path %s yielded no correct information screen. ' % path \
                + 'The output follows:\n%s' % info
                )
        type_ = type_matches.groups()[0].rstrip()
        out = {}
        out['type'] = type_
        block_matches = re.search('BLOCKS:(.*)TOTAL:', info, re.DOTALL)
        if block_matches:
            block_txt = block_matches.groups()[0].strip()
            block_specifiers = [x.split(':')[1] for x in block_txt.split(', ')]
            errmsg = 'Invalid block specifier %%s when stating file %s.' % path
            blocks = []
            for b in block_specifiers:
                if b.isdigit():
                    blocks.append(int(b))
                elif '-' in b:
                    pr = b.split('-')
                    if len(pr) > 2 or not all(el.isdigit() for el in pr):
                        raise Exception(errmsg % b)
                    blocks.extend(xrange(int(pr[0]), int(pr[1]) + 1))
                else:
                    raise Exception(errmsg % b)
            if blocks:
                out['blocks'] = blocks
            else:
                raise Exception(
                    'The file %s has no blocks specified!' % path
                    )
        if type_ == 'directory':
            files = self.ls(path)
            out['files'] = files
        return out

    def perform_file_check(self, path):
        """ Checks a single file against bad blocks.
            Returns a list of paths to recurse into if the file is a directory.
            """
        info = self.get_path_info(path)
        ok = True
        bad_blocks = []
        if 'blocks' in info:
            bad_blocks = [
                block for block in info['blocks'] if
                not self.bad_blocks.block_ok(block)
                ]
        if bad_blocks:
            ok = False
            self.log.write('Found bad blocks in path %s:\n' % path)
            for block in bad_blocks:
                self.log.write('%d\n' % block)
        if info['type'] != 'directory':
            return ok, []
        if bad_blocks:
            self.log.write(
                'Not recursing into %s because of bad blocks.\n' % path
                )
            return ok, []
        return ok, [os.path.join(path, basename) for basename in info['files']
            if basename not in ['.', '..']
            ]

    def perform_check(self, paths):
        """ Checks a file against bad blocks. Recurses into directories, does
            not follow symlinks. Does not recurse into directories with bad
            blocks.

            This function is a generator, control is yielded after each file is
            processed. You can use it like this:
                for _ in fscheck.perform_check(...):
                    pass

            or alternatively:
                _ = list(fscheck.perform_check(...))

            You can also use the function start_check which wraps this
            function and can show progress updates.
            """
        self.paths = []
        self.paths.extend(paths)
        self.visited = []
        self.bad = []
        while self.paths:
            try:
                path = self.paths.pop()
                ok, new_paths = self.perform_file_check(path)
                if not ok:
                    self.bad.append(path)
                self.paths.extend(new_paths)
                self.visited.append(path)
                yield CONTINUE
            except KeyboardInterrupt:
                if path not in self.visited:
                    self.log.write('Interrupted while processing path:\n%s\n' %
                        path
                        )
                    self.paths.append(path)
                yield SUSPEND

    def progress_done(self, indent_level=0):
        """ Prints information about the files that have been checked. """
        indent = ' ' * indent_level
        format_ = '%sDone: %%s\n' % indent
        self.log.write(format_ % (
            len(self.visited),
            ))
        self.erroneous_path_stats(indent_level)
        if self.paths:
            self.log.write('%sNext path:\n%s%s\n' % (
                indent,
                indent,
                self.paths[-1],
                ))
        self.log.write('%spexpect retries: %d\n' % (
            indent,
            self.pexpect_retries,
            ))
        self.log.write('%sunique pexpect retries: %d\n' % (
            indent,
            self.pexpect_retries_unique,
            ))
        self.log.write('%spexpect restarts: %d\n' % (
            indent,
            self.pexpect_restarts,
            ))

    def progress_update(self):
        """ Prints a progress update to stderr. """
        format_ = 'Queued: %s\n'
        self.log.write(format_ % (
            len(self.paths),
            ))
        self.progress_done(2)

    def output_details(self):
        unnamed = map('\n '.join, self.unnamed_files)
        deleted = map('\n '.join, self.deleted_files)
        self.log.write(
            'Details of erroneous paths:\n' \
            + 'bad:\n%s\n' % '\n'.join(self.bad) \
            + 'unnamed:\n%s\n' % '\n'.join(unnamed) \
            + 'deleted:\n%s\n' % '\n'.join(deleted)
            )

    def erroneous_path_stats(self, indent_level):
        indent = ' ' * indent_level
        self.log.write(
            '%spaths: ' % indent \
            + 'bad: %d, ' % len(self.bad) \
            + 'unnamed: %d, ' % len(self.unnamed_files) \
            + 'deleted: %d\n' % len(self.deleted_files)
            )

    def final_update(self):
        """ The information shown after the check is done. """
        self.log.write('\nFinished.\n')
        self.progress_done()
        if self.bad:
            self.log.write('Found %d bad files.\n' % len(self.bad))
        else:
            self.log.write('No bad files found.\n')
        self.output_details()


    def run_check(self, updates=True):
        """ Runs the check coroutine. """
        for status in self.progress:
            self.processed_acc += 1
            if self.processed_acc % 100 == 0:
                self.processed_acc = 0
                if updates:
                    self.progress_update()
            if status == SUSPEND:
                return
            elif status == CONTINUE:
                continue
            raise Exception(
                'Coroutine returned invalid status %s\n' % repr(status)
                )

    interrupted = False

    def continue_check(self, updates=True):
        """ Continues an interrupted check.
            You can break out of this with ^C just like out of start_check.
            Parameter:
            updates - whether to print updates or not.
            """
        if self.interrupted:
            self.log.write('Resuming on path:\n%s\n' %
                self.paths[-1]
                )
        self.interrupted = True

        # Every time the process is interrupted, we need to create a new
        # debugfs instance. If pexpect was interrupted out of, there is no
        # guessing what state debugfs was in, so let's not try to guess at all.
        self.setup_debugfs()

        self.run_check(updates=updates)
        if updates:
            self.final_update()

    def start_check(self, paths, updates=True):
        """ Start a check from the path given and recurse into directories.
            You can use a KeyboardInterrupt (^C) to break out of this, and
            then resume the check with continue_check.()
            Parameters:
            path - the path to check
            updates - whether to print progress updates
            """
        if updates:
            self.log.write(
                'Checking paths:\n%s\nand recursing into subdirectories\n' % \
                    '\n'.join(paths)
                )
        self.progress = self.perform_check(paths)
        self.processed_acc = 0
        self.continue_check(updates=updates)
