include "cps.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wo.mm"
include "cdm.mm"
include "wral.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "ctsr.mm"
include "psss.mm"
include "wss.mm"
include "wi.mm"
include "inss1.mm"
include "dmss.mm"
include "ssralv.mm"
include "mp2b.mm"
include "ralimi.mm"
include "syl.mm"
include "wb.mm"
include "inss2.mm"
include "ax-mp.mm"
include "dmxpid.mm"
include "sseqtri.mm"
include "sseli.mm"
include "brinxp.mm"
include "ancoms.mm"
include "orbi12d.mm"
include "syl2an.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "sylib.mm"
include "anim12i.mm"
include "eqid.mm"
include "istsr2.mm"
include "3imtr4i.mm"

theorem tsrss
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. TosetRel -> ( R i^i ( A X. A ) ) e. TosetRel )

  proof
    cR
    cps
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @2
    @1
    cR
    wbr
    #
    wo
    #
    vy
    cR
    cdm
    #
    wral
    #
    vx
    @6
    wral
    #
    wa
    cR
    cA
    cA
    cxp
    #
    cin
    #
    cps
    wcel
    #
    @1
    @2
    @10
    wbr
    #
    @2
    @1
    @10
    wbr
    #
    wo
    #
    vy
    @10
    cdm
    #
    wral
    #
    vx
    @15
    wral
    #
    wa
    cR
    ctsr
    wcel
    @10
    ctsr
    wcel
    @0
    @11
    @8
    @17
    cA
    cR
    psss
    @8
    @5
    vy
    @15
    wral
    #
    vx
    @15
    wral
    #
    @17
    @8
    @7
    vx
    @15
    wral
    #
    @19
    @10
    cR
    wss
    #
    @15
    @6
    wss
    #
    @8
    @20
    wi
    cR
    @9
    inss1
    #
    @10
    cR
    dmss
    #
    @7
    vx
    @15
    @6
    ssralv
    mp2b
    @7
    @18
    vx
    @15
    @21
    @22
    @7
    @18
    wi
    @23
    @24
    @5
    vy
    @15
    @6
    ssralv
    mp2b
    ralimi
    syl
    @18
    @16
    vx
    @15
    @1
    @15
    wcel
    #
    @5
    @14
    vy
    @15
    @25
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    @5
    @14
    wb
    @2
    @15
    wcel
    @15
    cA
    @1
    @15
    @9
    cdm
    #
    cA
    @10
    @9
    wss
    @15
    @28
    wss
    cR
    @9
    inss2
    @10
    @9
    dmss
    ax-mp
    cA
    dmxpid
    sseqtri
    #
    sseli
    @15
    cA
    @2
    @29
    sseli
    @26
    @27
    wa
    @3
    @12
    @4
    @13
    @1
    @2
    cA
    cA
    cR
    brinxp
    @27
    @26
    @4
    @13
    wb
    @2
    @1
    cA
    cA
    cR
    brinxp
    ancoms
    orbi12d
    syl2an
    ralbidva
    ralbiia
    sylib
    anim12i
    vx
    vy
    cR
    @6
    @6
    eqid
    istsr2
    vx
    vy
    @10
    @15
    @15
    eqid
    istsr2
    3imtr4i
end
