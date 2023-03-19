
axiom df-coss
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cR: class R
  assert |- ,~ R = { <. x , y >. | E. u ( u R x /\ u R y ) }
end
