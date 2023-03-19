
axiom ax-hvdistr1
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( A .h ( B +h C ) ) = ( ( A .h B ) +h ( A .h C ) ) )
end
