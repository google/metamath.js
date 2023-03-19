
axiom ax-his1
  let cA: class A
  let cB: class B
  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A .ih B ) = ( * ` ( B .ih A ) ) )
end
