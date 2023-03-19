
axiom df-ply
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  assert |- Poly = ( x e. ~P CC |-> { f | E. n e. NN0 E. a e. ( ( x u. { 0 } ) ^m NN0 ) f = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) } )
end
