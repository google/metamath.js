
axiom df-supp
  let vx: setvar x
  let vz: setvar z
  let vi: setvar i
  assert |- supp = ( x e. _V , z e. _V |-> { i e. dom x | ( x " { i } ) =/= { z } } )
end
