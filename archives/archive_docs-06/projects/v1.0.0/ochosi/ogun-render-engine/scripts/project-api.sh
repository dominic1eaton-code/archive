#
#
#

# git
git init
git remote add origin git@gitlab.com:emchoro/ossain/oru/ogun-render-engine.git
git remote set-url origin git@gitlab.com:emchoro/ossain/oru/ogun-render-engine.git
git add .;git commit -am "initial commit";git push origin main


# documentation
doxygen -g

# build
cd build
cmake ..
cmake --build . --config Release
cmake --install --prefix="" .

# run valgrind
EXECUTABLE="./src/Test/ApataDB"
RESULTS_FILE="valgrind-out.txt"
valgrind --leak-check=full \
         --show-leak-kinds=all \
         --track-origins=yes \
         --verbose \
         --log-file=${RESULTS_FILE} \
         ${EXECUTABLE}

# run cppcheck
cppcheck --enable=all \
         --xml \
         --suppressions-list=config/cppcheck.supress \
         src > cppcheck.results 2>&1 cppcheck.error

