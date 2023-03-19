include "cps.mm"
include "wcel.mm"
include "cxp.mm"
include "cin.mm"
include "wrel.mm"
include "ccom.mm"
include "wss.mm"
include "ccnv.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "inss1.mm"
include "psrel.mm"
include "relss.mm"
include "mpsyl.mm"
include "pstr2.mm"
include "trinxp.mm"
include "syl.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "uniin.mm"
include "unissi.mm"
include "sstri.mm"
include "elin.mm"
include "unixpid.mm"
include "eleq2i.mm"
include "simprr.mm"
include "cdm.mm"
include "crn.mm"
include "psdmrn.mm"
include "simpld.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "eqid.mm"
include "psref.mm"
include "syldan.mm"
include "adantrr.mm"
include "brinxp2.mm"
include "syl3anbrc.mm"
include "expr.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "ralrimiv.mm"
include "ssralv.mm"
include "ssbri.mm"
include "psasym.mm"
include "3expib.mm"
include "syl2ani.mm"
include "alrimivv.mm"
include "asymref2.mm"
include "sylanbrc.mm"
include "cvv.mm"
include "w3a.mm"
include "wb.mm"
include "inex1g.mm"
include "isps.mm"
include "mpbir3and.mm"

theorem psss
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. PosetRel -> ( R i^i ( A X. A ) ) e. PosetRel )

  proof
    cR
    cps
    wcel
    #
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
    @2
    wrel
    #
    @2
    @2
    ccom
    @2
    wss
    #
    @2
    @2
    ccnv
    cin
    cid
    @2
    cuni
    #
    cuni
    #
    cres
    wceq
    #
    @2
    cR
    wss
    @0
    cR
    wrel
    @4
    cR
    @1
    inss1
    #
    cR
    psrel
    @2
    cR
    relss
    mpsyl
    @0
    cR
    cR
    ccom
    cR
    wss
    @5
    cR
    pstr2
    cA
    cR
    trinxp
    syl
    @0
    vx
    cv
    #
    @10
    @2
    wbr
    #
    vx
    @7
    wral
    #
    @10
    vy
    cv
    #
    @2
    wbr
    #
    @13
    @10
    @2
    wbr
    #
    wa
    @10
    @13
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @8
    @7
    cR
    cuni
    #
    cuni
    #
    @1
    cuni
    #
    cuni
    #
    cin
    #
    wss
    @0
    @11
    vx
    @22
    wral
    @12
    @7
    @18
    @20
    cin
    #
    cuni
    @22
    @6
    @23
    cR
    @1
    uniin
    unissi
    @18
    @20
    uniin
    sstri
    @0
    @11
    vx
    @22
    @10
    @22
    wcel
    @10
    @19
    wcel
    #
    @10
    @21
    wcel
    #
    wa
    @0
    @11
    @10
    @19
    @21
    elin
    @0
    @24
    @25
    @11
    @25
    @10
    cA
    wcel
    #
    @0
    @24
    wa
    @11
    @21
    cA
    @10
    cA
    unixpid
    eleq2i
    @0
    @24
    @26
    @11
    @0
    @24
    @26
    wa
    wa
    @26
    @26
    @10
    @10
    cR
    wbr
    #
    @11
    @0
    @24
    @26
    simprr
    #
    @28
    @0
    @24
    @27
    @26
    @0
    @24
    @10
    cR
    cdm
    #
    wcel
    #
    @27
    @0
    @30
    @24
    @0
    @29
    @19
    @10
    @0
    @29
    @19
    wceq
    cR
    crn
    @19
    wceq
    cR
    psdmrn
    simpld
    eleq2d
    biimpar
    @10
    cR
    @29
    @29
    eqid
    psref
    syldan
    adantrr
    @10
    @10
    cA
    cA
    cR
    brinxp2
    syl3anbrc
    expr
    syl5bi
    expimpd
    syl5bi
    ralrimiv
    @11
    vx
    @7
    @22
    ssralv
    mpsyl
    @0
    @17
    vx
    vy
    @14
    @0
    @10
    @13
    cR
    wbr
    #
    @13
    @10
    cR
    wbr
    #
    @16
    @15
    @2
    cR
    @10
    @13
    @9
    ssbri
    @2
    cR
    @13
    @10
    @9
    ssbri
    @0
    @31
    @32
    @16
    @10
    @13
    cR
    psasym
    3expib
    syl2ani
    alrimivv
    vx
    vy
    @2
    asymref2
    sylanbrc
    @0
    @2
    cvv
    wcel
    @3
    @4
    @5
    @8
    w3a
    wb
    cR
    @1
    cps
    inex1g
    cvv
    @2
    isps
    syl
    mpbir3and
end
