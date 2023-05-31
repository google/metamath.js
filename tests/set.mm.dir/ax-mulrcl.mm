

axiom ax-mulrcl
  param cA: class A
  param cB: class B
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) e. RR )
end
