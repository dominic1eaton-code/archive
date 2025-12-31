#
#
# remote: - 6eafd403dc45c711398400d26e4f37417fa46f6c (460 MiB)
# remote: - e2b134ba874fcb2a6c57b58b3ec58d8d0062651b (118 MiB)
# remote: - 0930a8bd2ac8dce5178e64ee5162ff7362eeb7a8 (355 MiB)
# remote:
# remote: To resolve this error, you must either reduce the size of the above blobs, or utilize LFS.
# remote: You may use "git ls-tree -r HEAD | grep $BLOB_ID" to see the file path.
# remote:
# $ git ls-tree -r HEAD | grep 6eafd403dc45c711398400d26e4f37417fa46f6c
# 100644 blob 6eafd403dc45c711398400d26e4f37417fa46f6c    0.0.2/notes/Presentations/AVSIM_presentation/FinalPresentation_AVSIM.pptx
# 
# domni@DESKTOP-NOMF5O2 MINGW64 /d/dev/ws/archive_docs (main)
# $ git ls-tree -r HEAD | grep e2b134ba874fcb2a6c57b58b3ec58d8d0062651b
# 100644 blob e2b134ba874fcb2a6c57b58b3ec58d8d0062651b    0.0.2/notes/snippets/PlatoonController/untitled/results/bard.h5
# 
# domni@DESKTOP-NOMF5O2 MINGW64 /d/dev/ws/archive_docs (main)
# $ git ls-tree -r HEAD | grep 0930a8bd2ac8dce5178e64ee5162ff7362eeb7a8

git ls-tree -r HEAD | grep
git ls-tree -r HEAD | grep 6eafd403dc45c711398400d26e4f37417fa46f6c
git ls-tree -r HEAD | grep e2b134ba874fcb2a6c57b58b3ec58d8d0062651b
git ls-tree -r HEAD | grep 0930a8bd2ac8dce5178e64ee5162ff7362eeb7a8



scoop install git-lfs
git lfs install


git lfs track "*.pptx"
git lfs track "*.h5"
git lfs track "*.hdf5"


git filter-repo --forget-blob 6eafd403dc45c711398400d26e4f37417fa46f6c
git filter-repo --forget-blob e2b134ba874fcb2a6c57b58b3ec58d8d0062651b
git filter-repo --forget-blob 0930a8bd2ac8dce5178e64ee5162ff7362eeb7a8