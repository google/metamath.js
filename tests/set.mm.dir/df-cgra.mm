
axiom df-cgra
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- cgrA = ( g e. _V |-> { <. a , b >. | [. ( Base ` g ) / p ]. [. ( hlG ` g ) / k ]. ( ( a e. ( p ^m ( 0 ..^ 3 ) ) /\ b e. ( p ^m ( 0 ..^ 3 ) ) ) /\ E. x e. p E. y e. p ( a ( cgrG ` g ) <" x ( b ` 1 ) y "> /\ x ( k ` ( b ` 1 ) ) ( b ` 0 ) /\ y ( k ` ( b ` 1 ) ) ( b ` 2 ) ) ) } )
end
