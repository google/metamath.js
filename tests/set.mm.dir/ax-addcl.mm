
axiom ax-addcl
  let cA: class A
  let cB: class B
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) e. CC )
end
