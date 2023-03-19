include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "cossxp.mm"
include "dmexg.mm"
include "rnexg.mm"
include "xpexg.mm"
include "syl2anr.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem coexg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> ( A o. B ) e. _V )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    cA
    cB
    ccom
    #
    cB
    cdm
    #
    cA
    crn
    #
    cxp
    #
    wss
    @5
    cvv
    wcel
    #
    @2
    cvv
    wcel
    cA
    cB
    cossxp
    @1
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    @0
    cB
    cW
    dmexg
    cA
    cV
    rnexg
    @3
    @4
    cvv
    cvv
    xpexg
    syl2anr
    @2
    @5
    cvv
    ssexg
    sylancr
end
