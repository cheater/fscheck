#!/usr/bin/python
"""
    NAME

    fscheck
    a module for Python

    ABOUT THIS PROGRAM

    A consistency check for checking what files were made unavailable by bad
    sectors.

    Say you have a disk with bad sectors, you copy the partitions off it using
    gddrescue. You don't know what files were broken or made unavailable by
    directory inodes becoming corrupt. This program scans the directories,
    starting with an initial set (for example the root directory or a list of
    specific directories) and recurs into them, checking for errors. It does
    not list erroneous files.

    This program is used as a Python module which you import into the
    interpreter.  You instantiate the FSCheck class and feed it a gddrescue
    log. It uses debugfs (the ext3 filesystem debugger interpreter, not the
    kernel debugging tool) through a fairly finicky but surprisingly solid
    pexpect integration. It is very slow because it needs to save out a file
    for every command! There is no python interface for any debugfs-like
    functionality, alas.

    It's fairly conservative with resources, even with 30k files scanned
    the Python interpreter running it takes no more than 50 megabytes memory.

    USAGE

    You can either write a wrapper program around the fscheck module, or you
    can use it from the interpreter. Either way, you need to be running the
    python interpreter as root. The general operation will look like so:

    >>> import fscheck
    >>> B = fscheck.BadBlocks(file('gddrescue.log'))
    >>> C = fscheck.FSCheck(B, '/dev/sdf1')
    >>> ' '.join(C.dispatch.workers[0].ls('/')) # this is not supported,
                                                # but works for now
    '. .. lost+found var etc media cdrom' # and so on
    >>> C.start_check(['/opt']) # check /opt and all subdirs
    ^C # Interrupt at any time
    >>> C.paths
    [ ... paths queued for checking ... ]
    >>> print C.dispatch.cmd('stat "/"') # gets output from debugfs
    >>> C.continue_check()

    If the FSCheck's pexpect based communication to debugfs fails very badly,
    then it will fall back to asking you for interactive input. This usually
    works out well and barely ever happens.

    You can also interrupt start_check with Ctrl-C and then continue using
    continue_check which you can again interrupt. You might want to do that
    to check the state of the process, for example see what paths are queued
    up for being checked or what files have been found to have errors in them.

    If you want to dig deeper you can use the FSCheck.perform_check method
    which is a coroutine/generator that yields control after each file
    that it tests. The generator can be suspended at any time with Ctrl-C,
    it doesn't lose track of the file being processed at the moment.

    Finally, you can use the DebugFSDispatcher class as a direct Python
    interface into ext3 debugfs. It's relatively slow but better than
    nothing! The cmd method returns text, which you have to parse yourself. The
    text put out by debugfs is usually easy to parse. It is useful to make
    note of the amount of spaces between different output columns.

    You can also use BadBlocks as a python interface/parser for gddrescue logs.
    It cannot write out new gddrescue format logs but thanks to the format
    it is super easy to do.

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

class ListWithTodo(list):
    todo = 0

import tempfile, os, re, sys, pexpect, time, subprocess
class DebugFSDispatcher(object):
    """ This class dispatches all the work to debugfs.
        """

    responses = []
    queued_comms = ListWithTodo()
    def path_info_comm(self, path):
        """ Returns a communication tuple to put in the communication queue.
            """
        return (1, 'path_info', [path])

    def queue_path_infos(self, paths):
        """ Delegates the work for the paths given.
            """
        self.queue_comms(map(self.path_info_comm, paths))

    def receive_path_infos(self):
        """ Receives the results of work done for processing the path infos.
            """
        return self.receive_responses('path_info')

    known_responses = {
        (1, 'pexpect_restart'): None,
        (1, 'pexpect_retry'): None,
        (1, 'pexpect_retry_unique'): None,
        (1, 'path_info'): None,
        (1, 'deleted_file'): None,
        (1, 'unnamed_file'): None,
        }
    def receive_responses(self, topic):
        """ Receives responses on a certain topic.
            """
        unused_responses = []
        responses = []
        searched_response = (1, topic)
        while self.responses:
            response = self.responses.pop()
            response_id = response[0:2]
            if searched_response == response_id:
                responses.append(response[2])
            else:
                # This may be a bad place for such a check, maybe this code
                # should be somewhere else...
                if response_id not in self.known_responses:
                    raise UnknownResponse(repr(response))
                unused_responses.append(response)
        self.responses.extend(unused_responses)
        return responses
    def check_responses(self):
        """ Checks if the responses are OK.
            """
        # FIXME: this and receive_responses aren't most beautiful.
        self.receive_responses(None)

    def synchronize_workers(self):
        """ Synchronizes workers.

            This is only needed for synchronous communication where we have to
            explicitly give the workers some time on the interpreter. In a
            multiprocessing scheme this is unnecessary since they synchronize
            themselves because their interpreters run asynchronously to the one
            running this DebugFSDispatcher.
            """
        for worker in self.workers:
            worker.synchronize()

    def queue_comms(self, cmds):
        """ Queues commands to be communicated to the workers.
            """
        self.queued_comms.extend(cmds)
        self.queued_comms.todo += len(cmds)
        self.synchronize_workers()

    def done(self):
        """ Blocks until all queued communications are processed, then tells
            the caller whether it was done already.
            """
        self.check_responses()
        if self.responses:
            return False
        if self.queued_comms.todo > 0:
            return False
        self.join()
        if self.responses:
            return False
        return True

    def join(self):
        """ Blocks until all incoming commands are processed.
            """
        while self.queued_comms.todo > 0:
            self.synchronize_workers()

    workers = []
    def reset(self):
        """ Lets the Dispatcher know that it should set up its workers anew.
            """
        self.workers = [
            DebugFSWrapperWithCat(
                self.log,
                self.partition,
                self.responses,
                self.queued_comms,
                )
            for _ in range(1)
            ]

    _deleted_files = []
    _unnamed_files = []
    def get_suspect_files(self):
        """ Gets the list of encountered files without name and deleted files.
            """
        self._deleted_files.extend( self.receive_responses('deleted_file'))
        self._unnamed_files.extend( self.receive_responses('unnamed_file'))
        return {
            'unnamed': self._unnamed_files,
            'deleted': self._deleted_files,
            }
    _pexpect_restarts = 0
    _pexpect_retries = 0
    _pexpect_retries_unique = 0
    def get_pexpect_debug_info(self):
        """ Tells you how pexpect is behaving in the workers.
            """
        self._pexpect_restarts += len(
            self.receive_responses('pexpect_restart')
            )
        self._pexpect_retries += len(
            self.receive_responses('pexpect_retry')
            )
        self._pexpect_retries_unique += len(
            self.receive_responses('pexpect_retry_unique')
            )

        return {
            'restarts': self._pexpect_restarts,
            'retries': self._pexpect_retries,
            'retries_unique': self._pexpect_retries_unique,
            }

    def __init__(self, log, partition):
        self.log = log
        self.partition = partition
        self.reset()

class UnknownCommunication(ValueError):
    """ Raised when an unknown communicaton is received.
        """

class RetryThisCommandException(Exception):
    """ Raised when a command did not execute properly for some weird reason.
        """

class DebugFSWrapper(object):
    """ A wrapper around DebugFS.
        """

    comms_dispatcher = {}
    def register_comms(self):
        """ Creates the API description for the communications.
            """
        self.comms_dispatcher.update({
            (1, 'path_info'): [self.get_path_info, (1, 'path_info')]
            })

    def dispatch_comm(self, comm):
        """ Dispatches a communication.
            """
        comm_id = comm[0:2]
        if comm[0] == 1 and comm_id in self.comms_dispatcher:
            function, identifier = self.comms_dispatcher[comm[0:2]][0:2]
            try:
                self.responses.append(identifier + (function(*comm[2]),))
            except RetryThisCommandException:
                self.log.write('retrying command.\n')
                self.setup_debugfs_on_error('Command failed to execute.')
                self.queued_comms.append(comm)
            return
        raise UnknownCommunication(repr(comm))

    def synchronize(self):
        """ Processes the incoming communications queue. Blocks until the queue
            is empty.
            """
        while self.queued_comms:
            cmd = self.queued_comms.pop()
            try:
                self.dispatch_comm(cmd)
            except KeyboardInterrupt:
                self.queued_comms.append(cmd)
                raise

            self.queued_comms.todo -= 1
            cmd = None

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
                    if inode == 0:
                        self.response('deleted_file', (path, line))
                        error = True
                    elif file_ == '':
                        self.log.write(
                            u'Found file without name:\n%s\n' % line \
                            + u'while listing the path:\n%s\n' % path \
                            + u'inode number: %d\n'
                            )
                        self.response('unnamed_file', (path, line))
                        error = True
                    if error:
                        continue
                    if '/' in file_:
                        file_ = u'\/'.join(file_.split('/'))
                    files.append(file_)
                except IndexError:
                    err = u'Invalid identifier for path %s:\n' % path \
                        + u'Identifier:\n%s\nFile_:\n%s\n' % line, repr(file_)
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
        screen = self.cmd('stat "%s"' % path)
        lines = screen.split('\n')
        type_matches = re.search('Type: (.*)Mode:', lines[0])
        if not type_matches:
            raise RetryThisCommandException(
                u'The path %s yielded no correct information screen. ' % path \
                + u'The output follows:\n%s' % screen
                )
        type_ = type_matches.groups()[0].rstrip()
        out = {}
        out['path'] = path
        out['type'] = type_
        block_matches = re.search('BLOCKS:(.*)TOTAL:', screen, re.DOTALL)
        if block_matches:
            block_txt = block_matches.groups()[0].strip()
            block_specifiers = [x.split(':')[1] for x in block_txt.split(', ')]
            errmsg = u'Invalid block specifier %%s when stating file %s.' % path
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
                    u'The file %s has no blocks specified!' % path
                    )
        out['new_paths'] = []
        if type_ == 'directory':
            files = self.ls(path)
            out['new_paths'] = [
                os.path.join(out['path'], basename)
                for basename in files
                if basename not in ['.', '..']
                ]
        return out

    def response(self, topic, content):
        """ Adds a response.
            """
        self.responses.append((1, topic, content,))

    def dummy_response(self, topic):
        """ Adds a dummy response with no data.
            """
        self.response(topic, None,)

    def setup_debugfs_on_error(self, dsc):
        """ Use this to restart debugfs when an error happens. Do not use
            during normal operation.
            """
        self.log.write(
            u'Restarting debugfs because of an error: %s\n' % dsc
            )
        self.setup_debugfs()
        self.dummy_response('pexpect_restart')

    def which(self, what):
        """ Runs the which command to expand paths to programs.
            """
        which = subprocess.Popen(
            ['which', what],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            )
        path = which.stdout.read().strip()
        return path

    def __init__(
        self,
        log,
        partition,
        responses,
        queued_comms,
        pager=None,
        ):
        if not pager:
            pager = self.which('less')
        os.environ['DEBUGFS_PAGER'] = pager
        tests = {'-b': 'a block special device', '-r': 'readable'}
        for flag, dsc in tests.iteritems():
            if subprocess.call(['test', flag, partition]) is not 0:
                raise ValueError(u'The path "%s" is not %s.' % (partition, dsc))
        self.log = log
        self.partition = partition
        self.responses = responses
        self.queued_comms = queued_comms
        self.setup_debugfs()
        self.register_comms()

    def setup_debugfs(self):
        """ Sets up a fresh instance of debugfs and the communication dir. """
        self.debugfs = pexpect.spawn('debugfs %s' % self.partition)
        self.wait_prompt_unsafe()
        if self.dir_:
            rmrf(self.dir_)
        self.dir_ = tempfile.mkdtemp()

    dir_ = None

    def wait_prompt_unsafe(self):
        self.debugfs.expect('debugfs:  ')

    def wait_prompt(self):
        """ Wait for the debugfs prompt. """
        try:
            self.wait_prompt_unsafe()
        except pexpect.EOF:
            self.setup_debugfs_on_error(
                'EOF received while waiting for prompt.'
                )

    def sleep(self, tries):
        """ Sleeps for a certain amount of time so that pexpect can catch up.
            """
        if tries > 0:
            period = 0.05 * (tries ** 2)
            try:
                self.debugfs.expect(pexpect.EOF, timeout=period)
            except pexpect.TIMEOUT:
                pass

    def cmd(self, qry):
        """ Runs a command which results in the use of a pager, and returns
            the output as a string.
            """
        file_ = os.path.join(self.dir_, 'out')
        tries = 0
        if os.path.exists(file_):
            rmrf(file_)
        while True:
            try:
                self.debugfs.sendline(qry)
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
                self.setup_debugfs_on_error(
                    'Received EOF while sending commands.'
                    )
            tries += 1
            limit = 8

            self.dummy_response('pexpect_retry')
            if tries == 1:
                self.dummy_response('pexpect_retry_unique')

            if tries > limit:
                self.log.write(
                    u'Aborting after %d tries. Please input path to ' % limit \
                    + u'file in order to manually override. The command is:\n' \
                    + u'%s\n' % qry
                    )
                while True:
                    path = raw_input('> ')
                    if os.path.exists(path):
                        self.setup_debugfs_on_error('Manual entry fallback.')
                        return file(path).read()
                    self.log.write(
                        u'Could not find path %s. Please enter a path.\n'
                        )

            if tries > 2:
                self.log.write(
                    u'Could not get output data for command:\n%s\n' % qry \
                    + u'Retrying, attempt #%d\n' % tries
                    )
                self.log.write(u'Temporary directory:\n%s\nExists: %s\n' % (
                    self.dir_,
                    os.path.exists(self.dir_),
                    ))
            if tries > 6:
                self.log.write(u'Printing more debug info because there were ' \
                    + u'too many retries.\n'
                    )
                try:
                    self.debugfs.expect(pexpect.EOF, timeout=30)
                except pexpect.TIMEOUT:
                    pass
                self.log.write(u'Before:\n%s\nAfter:\n%s\n' % (
                    self.debugfs.before,
                    self.debugfs.after
                    ))
            if tries > 4:
                self.setup_debugfs_on_error(u'More than 4 retries.')

class DebugFSWrapperWithCat(DebugFSWrapper):
    """ This one uses cat for the pager, making the pexpect interaction easier
        and faster at the same time.
        """

    def setup_debugfs(self, *args, **kwargs):
        """ Sets up a fresh instance of debugfs and the communication dir. """
        out = super(DebugFSWrapperWithCat, self).setup_debugfs(*args, **kwargs)
        self.debugfs.delaybeforesend = 0
        return out

    def cmd(self, qry):
        """ Runs a command which results in the use of a pager, and returns
            the output as a string.
            """
        try:
            self.debugfs.sendline(qry)
            self.wait_prompt_unsafe()
            out = self.debugfs.before
            return u'\n'.join(out.split('\n')[1:])
        except (pexpect.TIMEOUT, pexpect.EOF):
            raise RetryThisCommandException()

    def __init__(self, *args, **kwargs):
        """ Among others we need to set the env var DEBUGFS_PAGER to the path
            to the cat binary.
            """
        kwargs['pager'] = self.which('cat')
        return super(DebugFSWrapperWithCat, self).__init__(*args, **kwargs)


CONTINUE = 0
SUSPEND = 1

import sys, codecs
class FSCheck(object):
    """ This class contains info about all the files and also contains the
        test and traversal logic.
        """

    log = codecs.getwriter('utf8')(sys.stderr)

    def __init__(self, bad_blocks, partition):
        self.dispatch = DebugFSDispatcher(
            log=self.log,
            partition=partition,
            )
        self.bad_blocks = bad_blocks

    def file_is_ok(self, info):
        """ Checks a single file against bad blocks.
            Returns a list of paths to recurse into if the file is a directory.
            """
        ok = True
        bad_blocks = []
        if 'blocks' in info:
            bad_blocks = [
                block for block in info['blocks'] if
                not self.bad_blocks.block_ok(block)
                ]
        if bad_blocks:
            ok = False
            self.log.write(u'Found bad blocks in path %s:\n' % info['path'])
            for block in bad_blocks:
                self.log.write(u'%d\n' % block)
        if info['type'] == 'directory' and bad_blocks:
            self.log.write(
                u'Not recursing into %s because of bad blocks.\n' %info['path']
                )
        return ok

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
        while True:
            if not self.paths and self.dispatch.done():
                break
            paths = infos = []
            try:
                # here we get multiple paths. also depends on how many are
                # sent out already.
                paths = [self.paths.pop() for _ in range(1) if self.paths]
                # here we will send out the paths for processing:
                self.dispatch.queue_path_infos(paths)
                # here we will receive fresh info objects:
                infos = self.dispatch.receive_path_infos()
                info = None
                while infos:
                    info = infos.pop()
                    if self.file_is_ok(info):
                        self.paths.extend(info['new_paths'])
                    else:
                        self.bad.append(info['path'])
                    info = None
                self.visited.extend(paths)
                yield CONTINUE
            except KeyboardInterrupt:
                self.log.write(u'\nAborting....\n')
                more_paths = [i['path'] for i in infos]
                if info:
                    more_paths.append(info['path'])
                self.dispatch.join()
                even_more_paths = [
                    i['path'] for i in
                    self.dispatch.receive_path_infos()
                    ]
                all_paths = paths + even_more_paths + more_paths
                self.log.write(u'Interrupted while processing paths:\n%s\n' %
                    u'\n'.join(all_paths)
                    )
                for path in paths + more_paths:
                    if path not in self.visited:
                        self.paths.extend(paths)
                yield SUSPEND

    def progress_done(self, indent_level=0):
        """ Prints information about the files that have been checked. """
        indent = ' ' * indent_level
        format_ = u'%sDone: %%s\n' % indent
        self.log.write(format_ % (
            len(self.visited),
            ))
        self.erroneous_path_stats(indent_level)
        if self.paths:
            self.log.write(u'%sNext path:\n%s%s\n' % (
                indent,
                indent,
                self.paths[-1],
                ))
        pexpect = self.dispatch.get_pexpect_debug_info()
        pexpect_labels = {
            'restarts': 'pexpect restarts',
            'retries': 'pexpect retries',
            'retries_unique': 'unique pexpect retries',
            }

        for k, v in pexpect.iteritems():
            self.log.write(u'%s%s: %d\n' % (indent, pexpect_labels[k], v,))

    def progress_update(self):
        """ Prints a progress update to stderr. """
        format_ = u'Queued: %s\n'
        self.log.write(format_ % (
            len(self.paths),
            ))
        self.progress_done(2)

    def output_details(self):
        suspect = self.dispatch.get_suspect_files()
        unnamed = map(u'\n '.join, suspect['unnamed'])
        deleted = map(u'\n '.join, suspect['deleted'])
        self.log.write(
            u'Details of erroneous paths:\n' \
            + u'bad:\n%s\n' % '\n'.join(self.bad) \
            + u'unnamed:\n%s\n' % '\n'.join(unnamed) \
            + u'deleted:\n%s\n' % '\n'.join(deleted)
            )

    def erroneous_path_stats(self, indent_level):
        suspect = self.dispatch.get_suspect_files()
        indent = ' ' * indent_level
        self.log.write(
            u'%spaths: ' % indent \
            + u'bad: %d, ' % len(self.bad) \
            + u'unnamed: %d, ' % len(suspect['unnamed']) \
            + u'deleted: %d\n' % len(suspect['deleted'])
            )

    def final_update(self):
        """ The information shown after the check is done. """
        self.log.write(u'\nFinished.\n')
        self.progress_done()
        if self.bad:
            self.log.write(u'Found %d bad files.\n' % len(self.bad))
        else:
            self.log.write(u'No bad files found.\n')
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
                u'Coroutine returned invalid status %s\n' % repr(status)
                )

    interrupted = False

    def continue_check(self, updates=True):
        """ Continues an interrupted check.
            You can break out of this with ^C just like out of start_check.
            Parameter:
            updates - whether to print updates or not.
            """
        if self.interrupted:
            self.log.write(u'Resuming on path:\n%s\n' %
                self.paths[-1]
                )
        self.interrupted = True

        # Every time the process is interrupted, we need to create a new
        # debugfs instance. If pexpect was interrupted out of, there is no
        # guessing what state debugfs was in, so let's not try to guess at all.
        self.dispatch.reset()

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
                u'Checking paths:\n%s\nand recursing into subdirectories\n' % \
                    u'\n'.join(paths)
                )
        self.progress = self.perform_check(paths)
        self.processed_acc = 0
        self.continue_check(updates=updates)
