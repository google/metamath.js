
axiom df-fwddifn
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  assert |- _/_\^n = ( n e. NN0 , f e. ( CC ^pm CC ) |-> ( x e. { y e. CC | A. k e. ( 0 ... n ) ( y + k ) e. dom f } |-> sum_ k e. ( 0 ... n ) ( ( n _C k ) x. ( ( -u 1 ^ ( n - k ) ) x. ( f ` ( x + k ) ) ) ) ) )
end
