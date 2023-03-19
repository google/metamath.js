
axiom df-fil
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  assert |- Fil = ( z e. _V |-> { f e. ( fBas ` z ) | A. x e. ~P z ( ( f i^i ~P x ) =/= (/) -> x e. f ) } )
end
