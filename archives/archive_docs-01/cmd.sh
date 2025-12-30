# commands
find . -type d -name ".git" -exec rm -rf {} +
find . -type f -size +100M -exec ls -lh {} \;

git lfs migrate import --include="$(find . -type f -size +100M -printf '%P,')"


