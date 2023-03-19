
axiom df-oppc
  let vz: setvar z
  let vu: setvar u
  let vf: setvar f
  assert |- oppCat = ( f e. _V |-> ( ( f sSet <. ( Hom ` ndx ) , tpos ( Hom ` f ) >. ) sSet <. ( comp ` ndx ) , ( u e. ( ( Base ` f ) X. ( Base ` f ) ) , z e. ( Base ` f ) |-> tpos ( <. z , ( 2nd ` u ) >. ( comp ` f ) ( 1st ` u ) ) ) >. ) )
end
