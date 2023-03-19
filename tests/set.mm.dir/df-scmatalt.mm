
axiom df-scmatalt
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vc: setvar c
  assert |- ScMatALT = ( n e. Fin , r e. _V |-> [_ ( n Mat r ) / a ]_ ( a |`s { m e. ( Base ` a ) | E. c e. ( Base ` r ) A. i e. n A. j e. n ( i m j ) = if ( i = j , c , ( 0g ` r ) ) } ) )
end
