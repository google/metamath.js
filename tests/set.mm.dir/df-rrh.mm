
axiom df-rrh
  let vr: setvar r
  assert |- RRHom = ( r e. _V |-> ( ( ( topGen ` ran (,) ) CnExt ( TopOpen ` r ) ) ` ( QQHom ` r ) ) )
end
