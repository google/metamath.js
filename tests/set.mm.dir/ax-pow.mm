
axiom ax-pow
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )
end
