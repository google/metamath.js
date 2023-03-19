
axiom ax-reg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ( E. y y e. x -> E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) )
end
