
axiom df-f
  let cA: class A
  let cB: class B
  let cF: class F
  assert |- ( F : A --> B <-> ( F Fn A /\ ran F C_ B ) )
end
