
axiom df-sum
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assert |- sum_ k e. A B = ( iota x ( E. m e. ZZ ( A C_ ( ZZ>= ` m ) /\ seq m ( + , ( n e. ZZ |-> if ( n e. A , [_ n / k ]_ B , 0 ) ) ) ~~> x ) \/ E. m e. NN E. f ( f : ( 1 ... m ) -1-1-onto-> A /\ x = ( seq 1 ( + , ( n e. NN |-> [_ ( f ` n ) / k ]_ B ) ) ` m ) ) ) )
end
