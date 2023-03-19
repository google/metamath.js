
axiom df-decpmat
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  assert |- decompPMat = ( m e. _V , k e. NN0 |-> ( i e. dom dom m , j e. dom dom m |-> ( ( coe1 ` ( i m j ) ) ` k ) ) )
end
