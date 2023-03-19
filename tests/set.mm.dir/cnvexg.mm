include "wcel.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "wrel.mm"
include "relcnv.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "df-rn.mm"
include "rnexg.mm"
include "syl5eqelr.mm"
include "dfdm4.mm"
include "dmexg.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem cnvexg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> `' A e. _V )

  proof
    cA
    cV
    wcel
    #
    cA
    ccnv
    #
    @1
    cdm
    #
    @1
    crn
    #
    cxp
    #
    wss
    #
    @4
    cvv
    wcel
    #
    @1
    cvv
    wcel
    @1
    wrel
    @5
    cA
    relcnv
    @1
    relssdmrn
    ax-mp
    @0
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    @6
    @0
    @2
    cA
    crn
    cvv
    cA
    df-rn
    cA
    cV
    rnexg
    syl5eqelr
    @0
    @3
    cA
    cdm
    cvv
    cA
    dfdm4
    cA
    cV
    dmexg
    syl5eqelr
    @2
    @3
    cvv
    cvv
    xpexg
    syl2anc
    @1
    @4
    cvv
    ssexg
    sylancr
end
