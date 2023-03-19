
axiom df-dsmm
  let vx: setvar x
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- (+)m = ( s e. _V , r e. _V |-> ( ( s Xs_ r ) |`s { f e. X_ x e. dom r ( Base ` ( r ` x ) ) | { x e. dom r | ( f ` x ) =/= ( 0g ` ( r ` x ) ) } e. Fin } ) )
end
