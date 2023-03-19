
axiom df-pclN
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assert |- PCl = ( k e. _V |-> ( x e. ~P ( Atoms ` k ) |-> |^| { y e. ( PSubSp ` k ) | x C_ y } ) )
end
