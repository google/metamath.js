
axiom ax-hvdistr2
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. CC /\ B e. CC /\ C e. ~H ) -> ( ( A + B ) .h C ) = ( ( A .h C ) +h ( B .h C ) ) )
end
