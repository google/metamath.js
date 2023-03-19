
axiom df-qus
  let vx: setvar x
  let ve: setvar e
  let vr: setvar r
  assert |- /s = ( r e. _V , e e. _V |-> ( ( x e. ( Base ` r ) |-> [ x ] e ) "s r ) )
end
