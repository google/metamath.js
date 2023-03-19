
axiom df-bj-moore
  let vx: setvar x
  let vy: setvar y
  assert |- Moore_ = { x | A. y e. ~P x ( U. x i^i |^| y ) e. x }
end
