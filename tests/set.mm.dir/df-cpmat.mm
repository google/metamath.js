
axiom df-cpmat
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- ConstPolyMat = ( n e. Fin , r e. _V |-> { m e. ( Base ` ( n Mat ( Poly1 ` r ) ) ) | A. i e. n A. j e. n A. k e. NN ( ( coe1 ` ( i m j ) ) ` k ) = ( 0g ` r ) } )
end
