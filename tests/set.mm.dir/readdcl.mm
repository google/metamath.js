include "ax-addrcl.mm"

theorem readdcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) e. RR )

  proof
    cA
    cB
    ax-addrcl
end
