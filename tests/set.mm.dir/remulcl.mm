include "ax-mulrcl.mm"

theorem remulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A x. B ) e. RR )

  proof
    cA
    cB
    ax-mulrcl
end
