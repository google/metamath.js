include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "wss.mm"
include "relcnv.mm"
include "relssdmrn.mm"
include "ax-mp.mm"
include "df-rn.mm"
include "dfdm4.mm"
include "xpeq12i.mm"
include "sseqtr4i.mm"

theorem cnvssrndm
  let cA: class A


  assert |- `' A C_ ( ran A X. dom A )

  proof
    cA
    ccnv
    #
    @0
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cA
    crn
    #
    cA
    cdm
    #
    cxp
    @0
    wrel
    @0
    @3
    wss
    cA
    relcnv
    @0
    relssdmrn
    ax-mp
    @4
    @1
    @5
    @2
    cA
    df-rn
    cA
    dfdm4
    xpeq12i
    sseqtr4i
end
