
axiom df-epi
  let vc: setvar c
  assert |- Epi = ( c e. Cat |-> tpos ( Mono ` ( oppCat ` c ) ) )
end
