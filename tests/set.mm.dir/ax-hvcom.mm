
axiom ax-hvcom
  let cA: class A
  let cB: class B
  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A +h B ) = ( B +h A ) )
end
