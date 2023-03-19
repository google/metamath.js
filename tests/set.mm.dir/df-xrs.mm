
axiom df-xrs
  let vx: setvar x
  let vy: setvar y
  assert |- RR*s = ( { <. ( Base ` ndx ) , RR* >. , <. ( +g ` ndx ) , +e >. , <. ( .r ` ndx ) , *e >. } u. { <. ( TopSet ` ndx ) , ( ordTop ` <_ ) >. , <. ( le ` ndx ) , <_ >. , <. ( dist ` ndx ) , ( x e. RR* , y e. RR* |-> if ( x <_ y , ( y +e -e x ) , ( x +e -e y ) ) ) >. } )
end
