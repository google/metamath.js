
axiom df-setc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  assert |- SetCat = ( u e. _V |-> { <. ( Base ` ndx ) , u >. , <. ( Hom ` ndx ) , ( x e. u , y e. u |-> ( y ^m x ) ) >. , <. ( comp ` ndx ) , ( v e. ( u X. u ) , z e. u |-> ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |-> ( g o. f ) ) ) >. } )
end
