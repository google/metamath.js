
axiom ax-his2
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h B ) .ih C ) = ( ( A .ih C ) + ( B .ih C ) ) )
end
