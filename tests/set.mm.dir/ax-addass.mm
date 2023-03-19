
axiom ax-addass
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )
end
