-module(testproj).

% -export([hello_world/0]).
-export([start/2]).

% hello_world() -> io::fwrite("running test service...\n").
start(_Type, _Args) ->
    {ok,self()}.
% start(_Type, _Args) -> :io.fwrite("running test service...\n").