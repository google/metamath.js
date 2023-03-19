include "wfun.mm"
include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "wrel.mm"
include "relco.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "dmcoss.mm"
include "dmexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "adantl.mm"
include "cres.mm"
include "rnco.mm"
include "rnexg.mm"
include "resfunexg.mm"
include "sylan2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "xpexg.mm"
include "syl2anc.mm"

theorem cofunexg
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Fun A /\ B e. C ) -> ( A o. B ) e. _V )

  proof
    cA
    wfun
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    cB
    ccom
    #
    @3
    cdm
    #
    @3
    crn
    #
    cxp
    #
    wss
    #
    @6
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @3
    wrel
    @7
    cA
    cB
    relco
    @3
    relssdmrn
    ax-mp
    @2
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    @8
    @1
    @9
    @0
    @1
    @4
    cB
    cdm
    #
    wss
    @10
    cvv
    wcel
    @9
    cA
    cB
    dmcoss
    cB
    cC
    dmexg
    @4
    @10
    cvv
    ssexg
    sylancr
    adantl
    @2
    @5
    cA
    cB
    crn
    #
    cres
    #
    crn
    #
    cvv
    cA
    cB
    rnco
    @2
    @12
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @1
    @0
    @11
    cvv
    wcel
    @14
    cB
    cC
    rnexg
    cA
    @11
    cvv
    resfunexg
    sylan2
    @12
    cvv
    rnexg
    syl
    syl5eqel
    @4
    @5
    cvv
    cvv
    xpexg
    syl2anc
    @3
    @6
    cvv
    ssexg
    sylancr
end
