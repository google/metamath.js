
axiom df-fn
  let cA: class A
  let cB: class B
  assert |- ( A Fn B <-> ( Fun A /\ dom A = B ) )
end
