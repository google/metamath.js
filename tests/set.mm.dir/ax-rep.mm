
axiom ax-rep
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- ( A. w E. y A. z ( A. y ph -> z = y ) -> E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) )
end
