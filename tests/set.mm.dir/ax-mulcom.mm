
axiom ax-mulcom
  let cA: class A
  let cB: class B
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. B ) = ( B x. A ) )
end
