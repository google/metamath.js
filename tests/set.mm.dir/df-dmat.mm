
axiom df-dmat
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- DMat = ( n e. Fin , r e. _V |-> { m e. ( Base ` ( n Mat r ) ) | A. i e. n A. j e. n ( i =/= j -> ( i m j ) = ( 0g ` r ) ) } )
end
