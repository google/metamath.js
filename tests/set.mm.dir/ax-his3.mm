
axiom ax-his3
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( ( A .h B ) .ih C ) = ( A x. ( B .ih C ) ) )
end
