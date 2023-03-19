
axiom df-xmul
  let vx: setvar x
  let vy: setvar y
  assert |- *e = ( x e. RR* , y e. RR* |-> if ( ( x = 0 \/ y = 0 ) , 0 , if ( ( ( ( 0 < y /\ x = +oo ) \/ ( y < 0 /\ x = -oo ) ) \/ ( ( 0 < x /\ y = +oo ) \/ ( x < 0 /\ y = -oo ) ) ) , +oo , if ( ( ( ( 0 < y /\ x = -oo ) \/ ( y < 0 /\ x = +oo ) ) \/ ( ( 0 < x /\ y = -oo ) \/ ( x < 0 /\ y = +oo ) ) ) , -oo , ( x x. y ) ) ) ) )
end
