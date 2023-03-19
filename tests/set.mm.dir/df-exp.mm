
axiom df-exp
  let vx: setvar x
  let vy: setvar y
  assert |- ^ = ( x e. CC , y e. ZZ |-> if ( y = 0 , 1 , if ( 0 < y , ( seq 1 ( x. , ( NN X. { x } ) ) ` y ) , ( 1 / ( seq 1 ( x. , ( NN X. { x } ) ) ` -u y ) ) ) ) )
end
