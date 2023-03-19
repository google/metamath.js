
axiom df-evlf
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  assert |- evalF = ( c e. Cat , d e. Cat |-> <. ( f e. ( c Func d ) , x e. ( Base ` c ) |-> ( ( 1st ` f ) ` x ) ) , ( x e. ( ( c Func d ) X. ( Base ` c ) ) , y e. ( ( c Func d ) X. ( Base ` c ) ) |-> [_ ( 1st ` x ) / m ]_ [_ ( 1st ` y ) / n ]_ ( a e. ( m ( c Nat d ) n ) , g e. ( ( 2nd ` x ) ( Hom ` c ) ( 2nd ` y ) ) |-> ( ( a ` ( 2nd ` y ) ) ( <. ( ( 1st ` m ) ` ( 2nd ` x ) ) , ( ( 1st ` m ) ` ( 2nd ` y ) ) >. ( comp ` d ) ( ( 1st ` n ) ` ( 2nd ` y ) ) ) ( ( ( 2nd ` x ) ( 2nd ` m ) ( 2nd ` y ) ) ` g ) ) ) ) >. )
end
