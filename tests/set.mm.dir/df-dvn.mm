
axiom df-dvn
  let vx: setvar x
  let vf: setvar f
  let vs: setvar s
  assert |- Dn = ( s e. ~P CC , f e. ( CC ^pm s ) |-> seq 0 ( ( ( x e. _V |-> ( s _D x ) ) o. 1st ) , ( NN0 X. { f } ) ) )
end
