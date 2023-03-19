
axiom ax-un
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y )
end
