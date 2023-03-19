
axiom df-cj
  let vx: setvar x
  let vy: setvar y
  assert |- * = ( x e. CC |-> ( iota_ y e. CC ( ( x + y ) e. RR /\ ( _i x. ( x - y ) ) e. RR ) ) )
end
