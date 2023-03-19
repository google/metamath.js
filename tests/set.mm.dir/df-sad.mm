
axiom df-sad
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vc: setvar c
  assert |- sadd = ( x e. ~P NN0 , y e. ~P NN0 |-> { k e. NN0 | hadd ( k e. x , k e. y , (/) e. ( seq 0 ( ( c e. 2o , m e. NN0 |-> if ( cadd ( m e. x , m e. y , (/) e. c ) , 1o , (/) ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) ) ` k ) ) } )
end
