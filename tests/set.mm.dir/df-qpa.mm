
axiom df-qpa
  let vf: setvar f
  let vn: setvar n
  let vr: setvar r
  let vp: setvar p
  let vd: setvar d
  assert |- _Qp = ( p e. Prime |-> [_ ( Qp ` p ) / r ]_ ( r polySplitLim ( n e. NN |-> { f e. ( Poly1 ` r ) | ( ( r deg1 f ) <_ n /\ A. d e. ran ( coe1 ` f ) ( `' d " ( ZZ \ { 0 } ) ) C_ ( 0 ... n ) ) } ) ) )
end
