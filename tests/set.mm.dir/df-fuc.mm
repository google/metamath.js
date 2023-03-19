
axiom df-fuc
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let va: setvar a
  let vb: setvar b
  assert |- FuncCat = ( t e. Cat , u e. Cat |-> { <. ( Base ` ndx ) , ( t Func u ) >. , <. ( Hom ` ndx ) , ( t Nat u ) >. , <. ( comp ` ndx ) , ( v e. ( ( t Func u ) X. ( t Func u ) ) , h e. ( t Func u ) |-> [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_ ( b e. ( g ( t Nat u ) h ) , a e. ( f ( t Nat u ) g ) |-> ( x e. ( Base ` t ) |-> ( ( b ` x ) ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. ( comp ` u ) ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) >. } )
end
