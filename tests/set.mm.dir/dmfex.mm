include "wf.mm"
include "wcel.mm"
include "cvv.mm"
include "cdm.mm"
include "wceq.mm"
include "wi.mm"
include "fdm.mm"
include "dmexg.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "syl.mm"
include "impcom.mm"

theorem dmfex
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F e. C /\ F : A --> B ) -> A e. _V )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cC
    wcel
    #
    cA
    cvv
    wcel
    #
    @0
    cF
    cdm
    #
    cA
    wceq
    #
    @1
    @2
    wi
    cA
    cB
    cF
    fdm
    @1
    @3
    cvv
    wcel
    @4
    @2
    cF
    cC
    dmexg
    @3
    cA
    cvv
    eleq1
    syl5ib
    syl
    impcom
end
