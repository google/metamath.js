
axiom df-yon
  let vc: setvar c
  assert |- Yon = ( c e. Cat |-> ( <. c , ( oppCat ` c ) >. curryF ( HomF ` ( oppCat ` c ) ) ) )
end
