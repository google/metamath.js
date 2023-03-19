
axiom ax-hvass
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A +h B ) +h C ) = ( A +h ( B +h C ) ) )
end
