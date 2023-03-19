
axiom df-rngc
  let vu: setvar u
  assert |- RngCat = ( u e. _V |-> ( ( ExtStrCat ` u ) |`cat ( RngHomo |` ( ( u i^i Rng ) X. ( u i^i Rng ) ) ) ) )
end
