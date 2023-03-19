include "wcel.mm"
include "wf1.mm"
include "cvv.mm"
include "cfn.mm"
include "crn.mm"
include "wb.mm"
include "cdm.mm"
include "wceq.mm"
include "wi.mm"
include "f1dm.mm"
include "dmexg.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibr.mm"
include "syl.mm"
include "impcom.mm"
include "f1dmvrnfibi.mm"
include "sylancom.mm"

theorem f1vrnfibi
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V


  assert |- ( ( F e. V /\ F : A -1-1-> B ) -> ( F e. Fin <-> ran F e. Fin ) )

  proof
    cF
    cV
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    cA
    cvv
    wcel
    #
    cF
    cfn
    wcel
    cF
    crn
    cfn
    wcel
    wb
    @1
    @0
    @2
    @1
    cF
    cdm
    #
    cA
    wceq
    #
    @0
    @2
    wi
    cA
    cB
    cF
    f1dm
    @0
    @2
    @4
    @3
    cvv
    wcel
    #
    cF
    cV
    dmexg
    @2
    @5
    wb
    cA
    @3
    cA
    @3
    cvv
    eleq1
    eqcoms
    syl5ibr
    syl
    impcom
    cA
    cB
    cF
    cvv
    f1dmvrnfibi
    sylancom
end
