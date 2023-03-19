
axiom df-bpoly
  let vx: setvar x
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  assert |- BernPoly = ( m e. NN0 , x e. CC |-> ( wrecs ( < , NN0 , ( g e. _V |-> [_ ( # ` dom g ) / n ]_ ( ( x ^ n ) - sum_ k e. dom g ( ( n _C k ) x. ( ( g ` k ) / ( ( n - k ) + 1 ) ) ) ) ) ) ` m ) )
end
