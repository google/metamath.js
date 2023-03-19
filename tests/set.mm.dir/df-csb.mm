
axiom df-csb
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assert |- [_ A / x ]_ B = { y | [. A / x ]. y e. B }
end
