include "chil.mm"
include "cva.mm"
include "ax-hfvadd.mm"
include "fovcl.mm"

theorem hvaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A +h B ) e. ~H )

  proof
    cA
    cB
    chil
    chil
    chil
    cva
    ax-hfvadd
    fovcl
end
