
axiom df-fo
  let cA: class A
  let cB: class B
  let cF: class F
  assert |- ( F : A -onto-> B <-> ( F Fn A /\ ran F = B ) )
end
