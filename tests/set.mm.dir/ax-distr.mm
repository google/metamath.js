
axiom ax-distr
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) )
end
