
axiom df-catc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  let vb: setvar b
  assert |- CatCat = ( u e. _V |-> [_ ( u i^i Cat ) / b ]_ { <. ( Base ` ndx ) , b >. , <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x Func y ) ) >. , <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |-> ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |-> ( g o.func f ) ) ) >. } )
end
