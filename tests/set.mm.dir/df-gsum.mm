
axiom df-gsum
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  assert |- gsum = ( w e. _V , f e. _V |-> [_ { x e. ( Base ` w ) | A. y e. ( Base ` w ) ( ( x ( +g ` w ) y ) = y /\ ( y ( +g ` w ) x ) = y ) } / o ]_ if ( ran f C_ o , ( 0g ` w ) , if ( dom f e. ran ... , ( iota x E. m E. n e. ( ZZ>= ` m ) ( dom f = ( m ... n ) /\ x = ( seq m ( ( +g ` w ) , f ) ` n ) ) ) , ( iota x E. g [. ( `' f " ( _V \ o ) ) / y ]. ( g : ( 1 ... ( # ` y ) ) -1-1-onto-> y /\ x = ( seq 1 ( ( +g ` w ) , ( f o. g ) ) ` ( # ` y ) ) ) ) ) ) )
end
