load("@rules_java//java:defs.bzl", "java_binary")

package(default_visibility = ["//visibility:public"])

java_binary(
    name = "ProjectRunner",
    srcs = glob(["src/main/java/com/example/*.java"]),
)

java_test(
    name = "ExampleTest",
    srcs = ["src/test/java/com/example/ExampleTest.java"],
    test_class = "com.example.ExampleTest",
)