
axiom df-sat
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let va: setvar a
  assert |- Sat = ( m e. _V , e e. _V |-> ( rec ( ( f e. _V |-> ( f u. { <. x , y >. | E. u e. f ( E. v e. f ( x = ( ( 1st ` u ) |g ( 1st ` v ) ) /\ y = ( ( m ^m _om ) \ ( ( 2nd ` u ) i^i ( 2nd ` v ) ) ) ) \/ E. i e. _om ( x = A.g i ( 1st ` u ) /\ y = { a e. ( m ^m _om ) | A. z e. m ( { <. i , z >. } u. ( a |` ( _om \ { i } ) ) ) e. ( 2nd ` u ) } ) ) } ) ) , { <. x , y >. | E. i e. _om E. j e. _om ( x = ( i e.g j ) /\ y = { a e. ( m ^m _om ) | ( a ` i ) e ( a ` j ) } ) } ) |` suc _om ) )
end
