#
#
#

# git configuration
git config --local user.name "Dominic Eaton"
git config --local user.email "eatondo000@gmail.com"


git clone git@gitlab.com:emchoro/moyo/ume/umuthi/umuthi-server.git
cd umuthi-server
git switch --create main
touch README.md
git add README.md
git commit -m "add README"
git push --set-upstream origin main


cd existing_repo
git remote rename origin old-origin
git remote add origin git@gitlab.com:emchoro/moyo/ume/umuthi/umuthi-config.git
git push --set-upstream origin --all
git push --set-upstream origin --tags



git init
git remote set-url origin git@gitlab.com:emchoro/moyo/ume/umuthi/umuthi-config.git
git add .;git commit -am "initial commit";git push origin main