
axiom df-prod
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assert |- prod_ k e. A B = ( iota x ( E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ E. n e. ( ZZ>= ` m ) E. y ( y =/= 0 /\ seq n ( x. , ( k e. ZZ |-> if ( k e. A , B , 1 ) ) ) ~~> y ) /\ seq m ( x. , ( k e. ZZ |-> if ( k e. A , B , 1 ) ) ) ~~> x ) \/ E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ x = ( seq 1 ( x. , ( n e. NN |-> [_ ( f ` n ) / k ]_ B ) ) ` m ) ) ) )
end
