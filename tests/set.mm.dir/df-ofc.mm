
axiom df-ofc
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vc: setvar c
  assert |- oFC R = ( f e. _V , c e. _V |-> ( x e. dom f |-> ( ( f ` x ) R c ) ) )
end
