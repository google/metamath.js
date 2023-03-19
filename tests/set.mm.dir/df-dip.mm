
axiom df-dip
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vk: setvar k
  assert |- .iOLD = ( u e. NrmCVec |-> ( x e. ( BaseSet ` u ) , y e. ( BaseSet ` u ) |-> ( sum_ k e. ( 1 ... 4 ) ( ( _i ^ k ) x. ( ( ( normCV ` u ) ` ( x ( +v ` u ) ( ( _i ^ k ) ( .sOLD ` u ) y ) ) ) ^ 2 ) ) / 4 ) ) )
end
