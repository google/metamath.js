
axiom df-zeta
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  assert |- zeta = ( iota_ f e. ( ( CC \ { 1 } ) -cn-> CC ) A. s e. ( CC \ { 1 } ) ( ( 1 - ( 2 ^c ( 1 - s ) ) ) x. ( f ` s ) ) = sum_ n e. NN0 ( sum_ k e. ( 0 ... n ) ( ( ( -u 1 ^ k ) x. ( n _C k ) ) x. ( ( k + 1 ) ^c s ) ) / ( 2 ^ ( n + 1 ) ) ) )
end
