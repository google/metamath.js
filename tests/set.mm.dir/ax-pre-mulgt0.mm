
axiom ax-pre-mulgt0
  let cA: class A
  let cB: class B
  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( 0 <RR A /\ 0 <RR B ) -> 0 <RR ( A x. B ) ) )
end
