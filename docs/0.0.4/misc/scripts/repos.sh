#
# repo batch processing script
# 

##
git init
for dir in */; do
  if [[ -d "$dir" ]]; then
    echo "Processing directory: $dir"
    # Add commands to process the directory here
    cd "$dir"
    mkdir .buildenv
    touch README.md LICENSE.md VERSION.md .gitignore .gitconfig .gitattributes .gitlab-ci.yml checksum project.json .buildenv/manifest.json
    git init
    git add .;git commit -am "initial commit"
    cd .. # Go back to the parent directory
    git submodule add ./$dir $dir
  fi
done

##
git init
for dir in */; do
  if [[ -d "$dir" ]]; then
    echo "Processing directory: $dir"
    # Add commands to process the directory here
    cd "$dir"
    mkdir .buildenv benchmarks src docs
    touch README.md LICENSE.md VERSION.md .gitignore .gitconfig .gitattributes .gitlab-ci.yml checksum project.json .buildenv/manifest.json
    git init
    git add .;git commit -am "initial commit"
    cd .. # Go back to the parent directory
    git submodule add ./$dir $dir
  fi
done

##
for dir in */; do
  if [[ -d "$dir" ]]; then
    echo "Processing directory: $dir"
    # cd "$dir"
    # git add .;git commit -am "initial commit"
    # cd ..
    git submodule add ./$dir $dir
  fi
done

git submodule foreach "git checkout -b develop; git add .;git commit -am \"update submodule structure\""
git submodule foreach --recursive "git checkout -b develop; git add .;git commit -am \"update submodule structure\""
git submodule foreach --recursive "git checkout -b develop"

