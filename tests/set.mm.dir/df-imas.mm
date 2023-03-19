
axiom df-imas
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- "s = ( f e. _V , r e. _V |-> [_ ( Base ` r ) / v ]_ ( ( { <. ( Base ` ndx ) , ran f >. , <. ( +g ` ndx ) , U_ p e. v U_ q e. v { <. <. ( f ` p ) , ( f ` q ) >. , ( f ` ( p ( +g ` r ) q ) ) >. } >. , <. ( .r ` ndx ) , U_ p e. v U_ q e. v { <. <. ( f ` p ) , ( f ` q ) >. , ( f ` ( p ( .r ` r ) q ) ) >. } >. } u. { <. ( Scalar ` ndx ) , ( Scalar ` r ) >. , <. ( .s ` ndx ) , U_ q e. v ( p e. ( Base ` ( Scalar ` r ) ) , x e. { ( f ` q ) } |-> ( f ` ( p ( .s ` r ) q ) ) ) >. , <. ( .i ` ndx ) , U_ p e. v U_ q e. v { <. <. ( f ` p ) , ( f ` q ) >. , ( p ( .i ` r ) q ) >. } >. } ) u. { <. ( TopSet ` ndx ) , ( ( TopOpen ` r ) qTop f ) >. , <. ( le ` ndx ) , ( ( f o. ( le ` r ) ) o. `' f ) >. , <. ( dist ` ndx ) , ( x e. ran f , y e. ran f |-> inf ( U_ n e. NN ran ( g e. { h e. ( ( v X. v ) ^m ( 1 ... n ) ) | ( ( f ` ( 1st ` ( h ` 1 ) ) ) = x /\ ( f ` ( 2nd ` ( h ` n ) ) ) = y /\ A. i e. ( 1 ... ( n - 1 ) ) ( f ` ( 2nd ` ( h ` i ) ) ) = ( f ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) } |-> ( RR*s gsum ( ( dist ` r ) o. g ) ) ) , RR* , < ) ) >. } ) )
end
