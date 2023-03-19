
axiom df-dmatalt
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  assert |- DMatALT = ( n e. Fin , r e. _V |-> [_ ( n Mat r ) / a ]_ ( a |`s { m e. ( Base ` a ) | A. i e. n A. j e. n ( i =/= j -> ( i m j ) = ( 0g ` r ) ) } ) )
end
