
axiom df-estrc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  assert |- ExtStrCat = ( u e. _V |-> { <. ( Base ` ndx ) , u >. , <. ( Hom ` ndx ) , ( x e. u , y e. u |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) >. , <. ( comp ` ndx ) , ( v e. ( u X. u ) , z e. u |-> ( g e. ( ( Base ` z ) ^m ( Base ` ( 2nd ` v ) ) ) , f e. ( ( Base ` ( 2nd ` v ) ) ^m ( Base ` ( 1st ` v ) ) ) |-> ( g o. f ) ) ) >. } )
end
