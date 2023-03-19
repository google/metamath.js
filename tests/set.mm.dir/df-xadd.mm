
axiom df-xadd
  let vx: setvar x
  let vy: setvar y
  assert |- +e = ( x e. RR* , y e. RR* |-> if ( x = +oo , if ( y = -oo , 0 , +oo ) , if ( x = -oo , if ( y = +oo , 0 , -oo ) , if ( y = +oo , +oo , if ( y = -oo , -oo , ( x + y ) ) ) ) ) )
end
