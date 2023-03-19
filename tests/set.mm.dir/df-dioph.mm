
axiom df-dioph
  let vu: setvar u
  let vt: setvar t
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  assert |- Dioph = ( n e. NN0 |-> ran ( k e. ( ZZ>= ` n ) , p e. ( mzPoly ` ( 1 ... k ) ) |-> { t | E. u e. ( NN0 ^m ( 1 ... k ) ) ( t = ( u |` ( 1 ... n ) ) /\ ( p ` u ) = 0 ) } ) )
end
