
axiom df-ringcALTV
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vb: setvar b
  assert |- RingCatALTV = ( u e. _V |-> [_ ( u i^i Ring ) / b ]_ { <. ( Base ` ndx ) , b >. , <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x RingHom y ) ) >. , <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |-> ( g e. ( ( 2nd ` v ) RingHom z ) , f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) ) |-> ( g o. f ) ) ) >. } )
end
