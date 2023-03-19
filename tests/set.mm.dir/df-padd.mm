
axiom df-padd
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vl: setvar l
  assert |- +P = ( l e. _V |-> ( m e. ~P ( Atoms ` l ) , n e. ~P ( Atoms ` l ) |-> ( ( m u. n ) u. { p e. ( Atoms ` l ) | E. q e. m E. r e. n p ( le ` l ) ( q ( join ` l ) r ) } ) ) )
end
