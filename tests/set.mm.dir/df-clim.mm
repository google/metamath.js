
axiom df-clim
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  assert |- ~~> = { <. f , y >. | ( y e. CC /\ A. x e. RR+ E. j e. ZZ A. k e. ( ZZ>= ` j ) ( ( f ` k ) e. CC /\ ( abs ` ( ( f ` k ) - y ) ) < x ) ) }
end
