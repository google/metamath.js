include "ax-mulrcl.mm"

theorem remulcl
  param cA: class A
  param cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) e. RR )

  proof
    cA
    cB
    ax-mulrcl
end
