
axiom df-atl
  let vx: setvar x
  let vk: setvar k
  let vp: setvar p
  assert |- AtLat = { k e. Lat | ( ( Base ` k ) e. dom ( glb ` k ) /\ A. x e. ( Base ` k ) ( x =/= ( 0. ` k ) -> E. p e. ( Atoms ` k ) p ( le ` k ) x ) ) }
end
