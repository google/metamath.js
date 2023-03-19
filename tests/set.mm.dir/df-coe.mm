
axiom df-coe
  let vz: setvar z
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  assert |- coeff = ( f e. ( Poly ` CC ) |-> ( iota_ a e. ( CC ^m NN0 ) E. n e. NN0 ( ( a " ( ZZ>= ` ( n + 1 ) ) ) = { 0 } /\ f = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) ) ) )
end
