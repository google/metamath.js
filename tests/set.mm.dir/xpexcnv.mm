include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "dmexg.mm"
include "dmxp.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "imp.mm"

theorem xpexcnv
  let cA: class A
  let cB: class B


  assert |- ( ( B =/= (/) /\ ( A X. B ) e. _V ) -> A e. _V )

  proof
    cB
    c0
    wne
    #
    cA
    cB
    cxp
    #
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    @1
    cdm
    #
    cvv
    wcel
    @0
    @3
    @1
    cvv
    dmexg
    @0
    @4
    cA
    cvv
    cA
    cB
    dmxp
    eleq1d
    syl5ib
    imp
end
