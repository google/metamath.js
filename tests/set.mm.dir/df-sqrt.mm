
axiom df-sqrt
  let vx: setvar x
  let vy: setvar y
  assert |- sqrt = ( x e. CC |-> ( iota_ y e. CC ( ( y ^ 2 ) = x /\ 0 <_ ( Re ` y ) /\ ( _i x. y ) e/ RR+ ) ) )
end
