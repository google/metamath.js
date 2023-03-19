
axiom df-rngcALTV
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vb: setvar b
  assert |- RngCatALTV = ( u e. _V |-> [_ ( u i^i Rng ) / b ]_ { <. ( Base ` ndx ) , b >. , <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x RngHomo y ) ) >. , <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |-> ( g e. ( ( 2nd ` v ) RngHomo z ) , f e. ( ( 1st ` v ) RngHomo ( 2nd ` v ) ) |-> ( g o. f ) ) ) >. } )
end
