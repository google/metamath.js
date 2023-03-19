
axiom df-frgr
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vg: setvar g
  let vk: setvar k
  let vl: setvar l
  assert |- FriendGraph = { g | ( g e. USGraph /\ [. ( Vtx ` g ) / v ]. [. ( Edg ` g ) / e ]. A. k e. v A. l e. ( v \ { k } ) E! x e. v { { x , k } , { x , l } } C_ e ) }
end
