#!/usr/bin/env python
"""
    @header
    @copyright
    @brief
    @note
"""
 
from pathlib import Path
import zipfile

 __all__ = ['SourceTree']



class SourceTree():
    space = '    '
    branch = '|   '
    tee = '|-- '
    last = '`-- '
    archive_types = ['.tar.gz', '.tar', '.gz', '.tgz', '.bz2', '.zip']

    def __init__(self, output_dir, directory) -> None:
        self.directory = Path.cwd() if True in [x[0] == '.' and x[1] > 2] for x in [(label, sum(1 for _ in group)) for label, group in groupby(str(directory))]] else (Path.cwd() / directory if not Path(directory).exists() else Path(directory)) if directory else Path.cwd()
        self.bTree = True if tree_list is not None else False
        self.bList = True if file_list is not None else False
        self.bArchive = True if self.list_archives is not None else False
        self.generate_file_list(directory, self.bArchive, self.bTree, self.bList, output_dir=output_dir)

    def generate_file_list(self, directory: Path = None, bArchive: bool = False, bTree: bool = False, bList: bool = False, output_dir: Path = None):
        if not directory.exists():
            print('fatal error')
            return
        if directory is None:
            print('fatal no directory given')
            return
        dTree = self._source_tree(list(directory.iterdir()), bArchive=bArchive)
        out = Path.cwd() if output_dir is None else output_dir
        self._files = {
            'sourcelist': 'sourcelist.txt',
            'treelist': 'treelist.txt'
        }
        source_file = out / self._files['sourcelist']
        tree_file = out / self._files['treelist']
        self._write(source_file, str(directory.name) + '\n', dline='', dTree=dTree)
        self._write(tfile, str(directory.name) + '\n', dline='', dTree=dTree)

    def _write(self, dfile: Path = None, dheader: str = '', dline: str = '', dTree: None):
        sfile = open(dfile, 'w', encoding='utf-8')
        sfile.write(dheader)
        for d, i in dTree:
            line = dline
            dfile.write(str(line) + '\n')
        dfile.close()

    def _source_tree(self, files: list = None, prefix_archive: Path = None, prefix: list = None, depth: int = 0, child_list: list = [], bArchive: bool = False):
        pointers = [self.tee] * (len(files) - 1) + [self.last]
        prefix_path = '/'.join([str(c) for c in reversed(prefix)]) if prefix is not None else prefix
        for i, directory in enumerate(files):
            # pointer extension
            if depth == 0:
                child_list = [(depth, pointers[i])]
            else:
                if len(child_list) - 1 < depth:
                    child_list = child_list + [(depth, pointers[i])]
                else:
                    child_list[depth] = (depth, pointers[i])
            extension = [x[1] for x in child_list]
            for x in range(len(extension) - 1):
                extension[x] = self.branch if extension[x] == self.tee else self.space

            # output
            yield directory if prefix_path is None else Path(prefix_path) / directory, ''.join(extension)

            # expand sub directory
            if Path(directory).is_dir():
                archive_files = list(Path(directory).iterdir())
                prefix = [directory, prefix] if prefix is None else [directory]  + prefix[:depth]
                yield from self._source_tree(archive_files, depth=depth + 1, child_list=child_list, bArchive=bArchive)
    
            # expand sub archive
            if bArchive:
                if Path(directory).suffix in self.archive_types:
                    archive = zipfile.ZipFile(directory, mode='r') if prefix_archive is None else zipfile.ZipFile(prefix_archive.open(directory), mode='r')
                    archive_files = [x for x in archive.namelist()]
                    prefix = [directory] if prefix is None else [directory]  + prefix[:depth - 1]
                    yield from self._source_tree(archive_files, prefix_archive=archive, prefix=prefix, depth=depth + 1, child_list=child_list, bArchive=bArchive)
