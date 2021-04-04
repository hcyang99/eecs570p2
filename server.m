type server_t : 0..1;
var lock : boolean;
var clients : array[server_t] of boolean;

ruleset idx : server_t do
    alias self : clients[idx]; other : clients[1 - idx] do
        rule "get connection"
            !self & !lock
        ==>
        begin
            lock := true;
            self := true;
        end;

        rule "keep connection"
            self
        ==>
        begin
        end;

        rule "release connection"
            self
        ==>
        begin
            self := false;
            lock := false;
        end;
    end;
endruleset;

startstate
    lock := false;
    for idx : server_t do
        clients[idx] := false;
    end;
end;

invariant "only one connection"
    forall idx : server_t do
        clients[idx] = true ->
        forall jdx : server_t do
            clients[jdx] = true -> idx = jdx
        end
    end;