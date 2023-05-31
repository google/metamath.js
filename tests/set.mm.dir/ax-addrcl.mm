

axiom ax-addrcl
  param cA: class A
  param cB: class B
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) e. RR )
end
