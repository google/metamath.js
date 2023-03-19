
axiom ax-inf
  param vf: var f
  assert |- T. |= ( ? \ f : ( ind -> ind ) . [ ( 1-1 f : ( ind -> ind ) ) /\ ( ~ ( onto f : ( ind -> ind ) ) ) ] )
end
