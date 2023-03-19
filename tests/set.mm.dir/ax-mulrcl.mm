
axiom ax-mulrcl
  let cA: class A
  let cB: class B
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) e. RR )
end
