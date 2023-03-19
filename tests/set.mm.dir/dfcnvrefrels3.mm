include "cid.mm"
include "cv.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cssr.mm"
include "ccnv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crels.mm"
include "ccnvrefrels.mm"
include "ccnvrefs.mm"
include "df-cnvrefrels.mm"
include "df-cnvrefs.mm"
include "abeqin.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "dmexg.mm"
include "elv.mm"
include "rnexg.mm"
include "xpex.mm"
include "inex2ALTV.mm"
include "brcnvssr.mm"
include "mp2b.mm"
include "inxpssidinxp.mm"
include "bitri.mm"
include "rabbieq.mm"

theorem dfcnvrefrels3
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r

  disjoint r x
  disjoint r y
  disjoint x y
  assert |- CnvRefRels = { r e. Rels | A. x e. dom r A. y e. ran r ( x r y -> x = y ) }

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
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    @7
    @8
    wceq
    wi
    vy
    @2
    wral
    vx
    @1
    wral
    #
    vr
    crels
    ccnvrefrels
    @6
    vr
    ccnvrefrels
    ccnvrefs
    crels
    df-cnvrefrels
    vr
    df-cnvrefs
    abeqin
    @6
    @5
    @4
    wss
    #
    @9
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    @10
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
    vx
    vy
    @1
    @2
    @0
    inxpssidinxp
    bitri
    rabbieq
end
