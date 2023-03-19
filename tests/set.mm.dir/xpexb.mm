include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "ccnv.mm"
include "cnvxp.mm"
include "cnvexg.mm"
include "syl5eqelr.mm"
include "impbii.mm"

theorem xpexb
  let cA: class A
  let cB: class B


  assert |- ( ( A X. B ) e. _V <-> ( B X. A ) e. _V )

  proof
    cA
    cB
    cxp
    #
    cvv
    wcel
    #
    cB
    cA
    cxp
    #
    cvv
    wcel
    #
    @1
    @2
    @0
    ccnv
    cvv
    cA
    cB
    cnvxp
    @0
    cvv
    cnvexg
    syl5eqelr
    @3
    @0
    @2
    ccnv
    cvv
    cB
    cA
    cnvxp
    @2
    cvv
    cnvexg
    syl5eqelr
    impbii
end
