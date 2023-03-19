
axiom df-rngisom
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- RngIsom = ( r e. _V , s e. _V |-> { f e. ( r RngHomo s ) | `' f e. ( s RngHomo r ) } )
end
