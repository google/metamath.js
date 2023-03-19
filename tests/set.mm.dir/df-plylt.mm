
axiom df-plylt
  let vx: setvar x
  let vs: setvar s
  let vp: setvar p
  assert |- Poly< = ( s e. ~P CC , x e. NN0 |-> { p e. ( Poly ` s ) | ( p = 0p \/ ( deg ` p ) < x ) } )
end
