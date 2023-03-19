
axiom df-homa
  let vx: setvar x
  let vc: setvar c
  assert |- HomA = ( c e. Cat |-> ( x e. ( ( Base ` c ) X. ( Base ` c ) ) |-> ( { x } X. ( ( Hom ` c ) ` x ) ) ) )
end
