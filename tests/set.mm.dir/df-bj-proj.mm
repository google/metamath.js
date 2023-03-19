
axiom df-bj-proj
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- ( A Proj B ) = { x | { x } e. ( B " { A } ) }
end
