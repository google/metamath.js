
axiom df-rngoiso
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- RngIso = ( r e. RingOps , s e. RingOps |-> { f e. ( r RngHom s ) | f : ran ( 1st ` r ) -1-1-onto-> ran ( 1st ` s ) } )
end
