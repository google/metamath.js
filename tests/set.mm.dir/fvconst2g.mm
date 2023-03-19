include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "fconstg.mm"
include "fvconst.mm"
include "sylan.mm"

theorem fvconst2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( B e. D /\ C e. A ) -> ( ( A X. { B } ) ` C ) = B )

  proof
    cB
    cD
    wcel
    cA
    cB
    csn
    #
    cA
    @0
    cxp
    #
    wf
    cC
    cA
    wcel
    cC
    @1
    cfv
    cB
    wceq
    cA
    cB
    cD
    fconstg
    cA
    cB
    cC
    @1
    fvconst
    sylan
end
