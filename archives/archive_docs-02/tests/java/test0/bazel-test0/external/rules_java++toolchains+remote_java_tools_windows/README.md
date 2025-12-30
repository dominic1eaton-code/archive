This Java tools version was built from the bazel repository at commit hash 2c844e79f6bb86702cde14fa7bb1f952b2c2c01f
using bazel version 8.1.1 on platform windows.
To build from source the same zip run the commands:

$ git clone https://github.com/bazelbuild/bazel.git
$ git checkout 2c844e79f6bb86702cde14fa7bb1f952b2c2c01f
$ bazel build //src:java_tools_prebuilt.zip
