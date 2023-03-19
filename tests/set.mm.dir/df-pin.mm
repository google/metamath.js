
axiom df-pin
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vj: setvar j
  let vn: setvar n
  let vp: setvar p
  assert |- piN = ( j e. Top , p e. U. j |-> ( n e. NN0 |-> ( ( 1st ` ( ( j OmN p ) ` n ) ) /s if ( n = 0 , { <. x , y >. | E. f e. ( II Cn j ) ( ( f ` 0 ) = x /\ ( f ` 1 ) = y ) } , ( ~=ph ` ( TopOpen ` ( 1st ` ( ( j OmN p ) ` ( n - 1 ) ) ) ) ) ) ) ) )
end
