-module(chat_app).
-behaviour(application).

-export([start/2]).
-export([stop/1]).
-export([hello/0]).


hello() -> io:fwrite("running chat service...\n").

start(_Type, _Args) ->
	chat_sup:start_link().

stop(_State) ->
	ok.
