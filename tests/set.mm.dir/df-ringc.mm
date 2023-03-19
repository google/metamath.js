
axiom df-ringc
  let vu: setvar u
  assert |- RingCat = ( u e. _V |-> ( ( ExtStrCat ` u ) |`cat ( RingHom |` ( ( u i^i Ring ) X. ( u i^i Ring ) ) ) ) )
end
