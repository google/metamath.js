
axiom df-risefac
  let vx: setvar x
  let vk: setvar k
  let vn: setvar n
  assert |- RiseFac = ( x e. CC , n e. NN0 |-> prod_ k e. ( 0 ... ( n - 1 ) ) ( x + k ) )
end
