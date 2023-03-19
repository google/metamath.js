
axiom df-symdif
  let cA: class A
  let cB: class B
  assert |- ( A /_\ B ) = ( ( A \ B ) u. ( B \ A ) )
end
