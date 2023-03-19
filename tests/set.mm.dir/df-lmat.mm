
axiom df-lmat
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  assert |- litMat = ( m e. _V |-> ( i e. ( 1 ... ( # ` m ) ) , j e. ( 1 ... ( # ` ( m ` 0 ) ) ) |-> ( ( m ` ( i - 1 ) ) ` ( j - 1 ) ) ) )
end
