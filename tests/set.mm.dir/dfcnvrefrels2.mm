include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cssr.mm"
include "ccnv.mm"
include "wbr.mm"
include "wss.mm"
include "ccnvrefrels.mm"
include "ccnvrefs.mm"
include "crels.mm"
include "df-cnvrefrels.mm"
include "df-cnvrefs.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "dmexg.mm"
include "elv.mm"
include "rnexg.mm"
include "xpex.mm"
include "inex2ALTV.mm"
include "brcnvssr.mm"
include "mp2b.mm"
include "wceq.mm"
include "elrels6.mm"
include "biimpi.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "abeqinbi.mm"

theorem dfcnvrefrels2
  let vr: setvar r


  assert |- CnvRefRels = { r e. Rels | r C_ ( _I i^i ( dom r X. ran r ) ) }

  proof
    cid
    vr
    cv
    #
    cdm
    #
    @0
    crn
    #
    cxp
    #
    cin
    #
    @0
    @3
    cin
    #
    cssr
    ccnv
    wbr
    #
    @0
    @4
    wss
    #
    vr
    ccnvrefrels
    ccnvrefs
    crels
    df-cnvrefrels
    vr
    df-cnvrefs
    @6
    @5
    @4
    wss
    #
    @0
    crels
    wcel
    #
    @7
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    @8
    wb
    @1
    @2
    @1
    cvv
    wcel
    vr
    @0
    cvv
    dmexg
    elv
    @2
    cvv
    wcel
    vr
    @0
    cvv
    rnexg
    elv
    xpex
    @3
    cid
    cvv
    inex2ALTV
    @4
    @5
    cvv
    brcnvssr
    mp2b
    @9
    @5
    @0
    @4
    @9
    @5
    @0
    wceq
    #
    @9
    @10
    wb
    vr
    @0
    cvv
    elrels6
    elv
    biimpi
    sseq1d
    syl5bb
    abeqinbi
end
