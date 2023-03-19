
axiom df-qpOLD
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vb: setvar b
  assert |- QpOLD = ( p e. Prime |-> [_ { h e. ( ZZ ^m ( 0 ... ( p - 1 ) ) ) | E. x e. ran ZZ>= ( `' h " ( ZZ \ { 0 } ) ) C_ x } / b ]_ ( ( { <. ( Base ` ndx ) , b >. , <. ( +g ` ndx ) , ( f e. b , g e. b |-> ( ( /Qp ` p ) ` ( f oF + g ) ) ) >. , <. ( .r ` ndx ) , ( f e. b , g e. b |-> ( ( /Qp ` p ) ` ( n e. ZZ |-> sum_ k e. ZZ ( ( f ` k ) x. ( g ` ( n - k ) ) ) ) ) ) >. } u. { <. ( le ` ndx ) , { <. f , g >. | ( { f , g } C_ b /\ sum_ k e. ZZ ( ( f ` -u k ) x. ( ( p + 1 ) ^ -u k ) ) < sum_ k e. ZZ ( ( g ` -u k ) x. ( ( p + 1 ) ^ -u k ) ) ) } >. } ) toNrmGrp ( f e. b |-> if ( f = ( ZZ X. { 0 } ) , 0 , ( p ^ -u sup ( ( `' f " ( ZZ \ { 0 } ) ) , RR , `' < ) ) ) ) ) )
end
