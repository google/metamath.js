
axiom df-toset
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vr: setvar r
  let vb: setvar b
  assert |- Toset = { f e. Poset | [. ( Base ` f ) / b ]. [. ( le ` f ) / r ]. A. x e. b A. y e. b ( x r y \/ y r x ) }
end
