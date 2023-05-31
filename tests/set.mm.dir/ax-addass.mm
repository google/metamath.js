

axiom ax-addass
  param cA: class A
  param cB: class B
  param cC: class C
  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )
end
