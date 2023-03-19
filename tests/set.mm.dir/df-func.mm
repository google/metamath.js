
axiom df-func
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vb: setvar b
  assert |- Func = ( t e. Cat , u e. Cat |-> { <. f , g >. | [. ( Base ` t ) / b ]. ( f : b --> ( Base ` u ) /\ g e. X_ z e. ( b X. b ) ( ( ( f ` ( 1st ` z ) ) ( Hom ` u ) ( f ` ( 2nd ` z ) ) ) ^m ( ( Hom ` t ) ` z ) ) /\ A. x e. b ( ( ( x g x ) ` ( ( Id ` t ) ` x ) ) = ( ( Id ` u ) ` ( f ` x ) ) /\ A. y e. b A. z e. b A. m e. ( x ( Hom ` t ) y ) A. n e. ( y ( Hom ` t ) z ) ( ( x g z ) ` ( n ( <. x , y >. ( comp ` t ) z ) m ) ) = ( ( ( y g z ) ` n ) ( <. ( f ` x ) , ( f ` y ) >. ( comp ` u ) ( f ` z ) ) ( ( x g y ) ` m ) ) ) ) } )
end
