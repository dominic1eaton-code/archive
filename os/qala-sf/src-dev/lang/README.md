# qala SDE language



# examples:
## example deployment script:

<code>
# @license
# @brief

def create();
    def deployment():
        def elixir(pm=mix):
            mix init
        
    def javascript(pm=angular):
        angular init
        npm init

    def cpp(pm=cmake):
        qamake init

    def erlang(pm=mix):
        mix init

    def electron():
        npm init

    def rails():
        rails init

    def django():
        django init

    def zig():
        zig init

    def rust():
        cargo init

    def go(pm=bazel):
        qala init go --pm=bazel

    def java(pm=bazel):
        qala init java --pm=bazel

    def scala(pm=sbt):
        sbt init

    def android():
        qala init android

    def kotlin():
        qala init kotlin

    def shell():
        qala init bash
        qala init batch
        qala init powershell

    def typescript():
        npm install --save-dev typescript
        npx tsc --init
</code>