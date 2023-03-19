include "wor.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "wwe.mm"
include "ccnv.mm"
include "wofi.mm"
include "cnvso.mm"
include "sylanb.mm"
include "jca.mm"
include "weso.mm"
include "adantr.mm"
include "coi.mm"
include "cdm.mm"
include "com.mm"
include "wss.mm"
include "cv.mm"
include "cep.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csuc.mm"
include "peano2.mm"
include "sucidg.mm"
include "wceq.mm"
include "vex.mm"
include "brcnv.mm"
include "epel.mm"
include "bitri.mm"
include "eleq2.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "dfrex2.mm"
include "sylib.mm"
include "nrex.mm"
include "word.mm"
include "wb.mm"
include "ordom.mm"
include "eqid.mm"
include "oicl.mm"
include "ordtri1.mm"
include "mp2an.mm"
include "cvv.mm"
include "wfr.mm"
include "c0.mm"
include "wne.mm"
include "con0.mm"
include "oion.mm"
include "mp1i.mm"
include "simpr.mm"
include "ssexd.mm"
include "wiso.mm"
include "oiiso.mm"
include "mpan.mm"
include "isocnv2.mm"
include "wefr.mm"
include "isofr.mm"
include "biimpar.mm"
include "syl2an.mm"
include "c1o.mm"
include "1onn.mm"
include "ne0i.mm"
include "fri.mm"
include "syl22anc.mm"
include "ex.mm"
include "syl5bir.mm"
include "mt3i.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "sylancl.mm"
include "cen.mm"
include "simpl.mm"
include "oien.mm"
include "sylancr.mm"
include "enfi.mm"
include "syl.mm"
include "mpbid.mm"
include "impbii.mm"

theorem wofib
  let cA: class A
  let cR: class R
  let vy: setvar y
  let vz: setvar z
  assume wofib.1: |- A e. _V


  assert |- ( ( R Or A /\ A e. Fin ) <-> ( R We A /\ `' R We A ) )

  proof
    cA
    cR
    wor
    #
    cA
    cfn
    wcel
    #
    wa
    #
    cA
    cR
    wwe
    #
    cA
    cR
    ccnv
    #
    wwe
    #
    wa
    #
    @2
    @3
    @5
    cA
    cR
    wofi
    @0
    cA
    @4
    wor
    @1
    @5
    cA
    cR
    cnvso
    cA
    @4
    wofi
    sylanb
    jca
    @6
    @0
    @1
    @3
    @0
    @5
    cA
    cR
    weso
    adantr
    @6
    cA
    cR
    coi
    #
    cdm
    #
    cfn
    wcel
    #
    @1
    @6
    @8
    com
    wcel
    #
    @8
    @8
    wss
    @9
    @6
    @10
    vz
    cv
    #
    vy
    cv
    #
    cep
    ccnv
    #
    wbr
    #
    wn
    vz
    com
    wral
    #
    vy
    com
    wrex
    #
    @15
    vy
    com
    @12
    com
    wcel
    #
    @14
    vz
    com
    wrex
    #
    @15
    wn
    @17
    @12
    csuc
    #
    com
    wcel
    @12
    @19
    wcel
    #
    @18
    @12
    peano2
    @12
    com
    sucidg
    @14
    @20
    vz
    @19
    com
    @14
    @12
    @11
    wcel
    #
    @11
    @19
    wceq
    @20
    @14
    @12
    @11
    cep
    wbr
    @21
    @11
    @12
    cep
    vz
    vex
    vy
    vex
    brcnv
    vy
    vz
    epel
    bitri
    @11
    @19
    @12
    eleq2
    syl5bb
    rspcev
    syl2anc
    @14
    vz
    com
    dfrex2
    sylib
    nrex
    @10
    wn
    #
    com
    @8
    wss
    #
    @6
    @16
    com
    word
    @8
    word
    @23
    @22
    wb
    ordom
    cA
    cR
    @7
    @7
    eqid
    #
    oicl
    com
    @8
    ordtri1
    mp2an
    @6
    @23
    @16
    @6
    @23
    wa
    #
    com
    cvv
    wcel
    @8
    @13
    wfr
    #
    @23
    com
    c0
    wne
    #
    @16
    @25
    com
    @8
    con0
    cA
    cvv
    wcel
    #
    @8
    con0
    wcel
    @25
    wofib.1
    cA
    cR
    @7
    cvv
    @24
    oion
    mp1i
    @6
    @23
    simpr
    #
    ssexd
    @6
    @26
    @23
    @3
    @8
    cA
    @13
    @4
    @7
    wiso
    #
    cA
    @4
    wfr
    #
    @26
    @5
    @3
    @8
    cA
    cep
    cR
    @7
    wiso
    #
    @30
    @28
    @3
    @32
    wofib.1
    cA
    cR
    @7
    cvv
    @24
    oiiso
    mpan
    @8
    cA
    cep
    cR
    @7
    isocnv2
    sylib
    cA
    @4
    wefr
    @30
    @26
    @31
    @8
    cA
    @13
    @4
    @7
    isofr
    biimpar
    syl2an
    adantr
    @29
    c1o
    com
    wcel
    @27
    @25
    1onn
    com
    c1o
    ne0i
    mp1i
    vy
    vz
    @8
    com
    cvv
    @13
    fri
    syl22anc
    ex
    syl5bir
    mt3i
    @8
    ssid
    @8
    @8
    ssnnfi
    sylancl
    @6
    @8
    cA
    cen
    wbr
    #
    @9
    @1
    wb
    @6
    @28
    @3
    @33
    wofib.1
    @3
    @5
    simpl
    cA
    cR
    @7
    cvv
    @24
    oien
    sylancr
    @8
    cA
    enfi
    syl
    mpbid
    jca
    impbii
end
