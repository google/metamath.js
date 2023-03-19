include "chil.mm"
include "cc.mm"
include "csm.mm"
include "ax-hfvmul.mm"
include "fovcl.mm"

theorem hvmulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( A .h B ) e. ~H )

  proof
    cA
    cB
    chil
    cc
    chil
    csm
    ax-hfvmul
    fovcl
end
