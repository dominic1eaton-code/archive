# Chat

**TODO: Add description**

## Installation


## Development
export PATH=$PATH:/d/Users/domni/scoop/apps/erlang/28.1.1/bin/

## run application
erl
chat_app:hello()
chat_app:start(0, 0)
chat_app:stop(0)


erl -noshell -s chat_app hello -s init stop
