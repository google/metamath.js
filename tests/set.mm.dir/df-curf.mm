
axiom df-curf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vc: setvar c
  let vd: setvar d
  assert |- curryF = ( e e. _V , f e. _V |-> [_ ( 1st ` e ) / c ]_ [_ ( 2nd ` e ) / d ]_ <. ( x e. ( Base ` c ) |-> <. ( y e. ( Base ` d ) |-> ( x ( 1st ` f ) y ) ) , ( y e. ( Base ` d ) , z e. ( Base ` d ) |-> ( g e. ( y ( Hom ` d ) z ) |-> ( ( ( Id ` c ) ` x ) ( <. x , y >. ( 2nd ` f ) <. x , z >. ) g ) ) ) >. ) , ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> ( g e. ( x ( Hom ` c ) y ) |-> ( z e. ( Base ` d ) |-> ( g ( <. x , z >. ( 2nd ` f ) <. y , z >. ) ( ( Id ` d ) ` z ) ) ) ) ) >. )
end
