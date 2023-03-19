
axiom df-pss
  let cA: class A
  let cB: class B
  assert |- ( A C. B <-> ( A C_ B /\ A =/= B ) )
end
