
axiom df-smu
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assert |- smul = ( x e. ~P NN0 , y e. ~P NN0 |-> { k e. NN0 | k e. ( seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. x /\ ( n - m ) e. y ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) ) ` ( k + 1 ) ) } )
end
