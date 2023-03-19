
axiom df-smat
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vl: setvar l
  assert |- subMat1 = ( m e. _V |-> ( k e. NN , l e. NN |-> ( m o. ( i e. NN , j e. NN |-> <. if ( i < k , i , ( i + 1 ) ) , if ( j < l , j , ( j + 1 ) ) >. ) ) ) )
end
