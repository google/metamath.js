include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "cceil.mm"
include "cfv.mm"
include "wceq.mm"
include "ceilid.mm"
include "ceilcl.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "impbid2.mm"

theorem ceilidz
  let cA: class A


  assert |- ( A e. RR -> ( A e. ZZ <-> ( |^ ` A ) = A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cceil
    cfv
    #
    cA
    wceq
    #
    cA
    ceilid
    @0
    @2
    cz
    wcel
    @3
    @1
    cA
    ceilcl
    @2
    cA
    cz
    eleq1
    syl5ibcom
    impbid2
end
