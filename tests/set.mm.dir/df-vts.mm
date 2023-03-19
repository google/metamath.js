
axiom df-vts
  let vx: setvar x
  let vn: setvar n
  let va: setvar a
  let vl: setvar l
  assert |- vts = ( l e. ( CC ^m NN ) , n e. NN0 |-> ( x e. CC |-> sum_ a e. ( 1 ... n ) ( ( l ` a ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( a x. x ) ) ) ) ) )
end
