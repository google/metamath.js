
axiom df-rmx
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  assert |- rmX = ( a e. ( ZZ>= ` 2 ) , n e. ZZ |-> ( 1st ` ( `' ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( a ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) ` ( ( a + ( sqrt ` ( ( a ^ 2 ) - 1 ) ) ) ^ n ) ) ) )
end
