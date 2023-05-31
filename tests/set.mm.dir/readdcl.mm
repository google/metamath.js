include "ax-addrcl.mm"

theorem readdcl
  param cA: class A
  param cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) e. RR )

  proof
    cA
    cB
    ax-addrcl
end
