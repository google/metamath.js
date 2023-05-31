

axiom ax-mulcl
  param cA: class A
  param cB: class B
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. B ) e. CC )
end
