
axiom df-fv
  let vx: setvar x
  let cA: class A
  let cF: class F
  assert |- ( F ` A ) = ( iota x A F x )
end
