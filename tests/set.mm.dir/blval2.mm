include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "csn.mm"
include "cxr.mm"
include "wceq.mm"
include "rpxr.mm"
include "blvalps.mm"
include "syl3an3.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "cop.mm"
include "wa.mm"
include "cxp.mm"
include "wb.mm"
include "wf.mm"
include "wfn.mm"
include "psmetf.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "3ad2ant1.mm"
include "opelxp.mm"
include "baib.mm"
include "3ad2ant2.mm"
include "biimpd.mm"
include "adantrd.mm"
include "simprl.mm"
include "ex.mm"
include "simpl2.mm"
include "syl.mm"
include "df-ov.mm"
include "eleq1i.mm"
include "cle.mm"
include "0xr.mm"
include "simpl3.mm"
include "rpxrd.mm"
include "elico1.mm"
include "sylancr.mm"
include "simpl1.mm"
include "simpr.mm"
include "psmetcl.mm"
include "syl3anc.mm"
include "psmetge0.mm"
include "jca.mm"
include "biantrurd.mm"
include "df-3an.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "syl5bbr.mm"
include "anbi12d.mm"
include "pm5.21ndd.mm"
include "cvv.mm"
include "vex.mm"
include "elimasng.mm"
include "mpan2.mm"
include "rabid.mm"
include "a1i.mm"
include "3bitr4d.mm"
include "eqrd.mm"
include "eqtr4d.mm"

theorem blval2
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vx: setvar x


  assert |- ( ( D e. ( PsMet ` X ) /\ P e. X /\ R e. RR+ ) -> ( P ( ball ` D ) R ) = ( ( `' D " ( 0 [,) R ) ) " { P } ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    crp
    wcel
    #
    w3a
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cP
    vx
    cv
    #
    cD
    co
    #
    cR
    clt
    wbr
    #
    vx
    cX
    crab
    #
    cD
    ccnv
    cc0
    cR
    cico
    co
    #
    cima
    #
    cP
    csn
    cima
    #
    @2
    @0
    @1
    cR
    cxr
    wcel
    #
    @4
    @8
    wceq
    cR
    rpxr
    vx
    cD
    cP
    cR
    cX
    blvalps
    syl3an3
    @3
    vx
    @11
    @8
    @3
    vx
    nfv
    vx
    @11
    nfcv
    @7
    vx
    cX
    nfrab1
    @3
    cP
    @5
    cop
    #
    @10
    wcel
    #
    @5
    cX
    wcel
    #
    @7
    wa
    #
    @5
    @11
    wcel
    #
    @5
    @8
    wcel
    #
    @3
    @14
    @13
    cX
    cX
    cxp
    #
    wcel
    #
    @13
    cD
    cfv
    #
    @9
    wcel
    #
    wa
    #
    @16
    @0
    @1
    @14
    @23
    wb
    #
    @2
    @0
    @19
    cxr
    cD
    wf
    cD
    @19
    wfn
    @24
    cD
    cX
    psmetf
    @19
    cxr
    cD
    ffn
    @19
    @13
    @9
    cD
    elpreima
    3syl
    3ad2ant1
    @3
    @15
    @23
    @16
    @3
    @20
    @15
    @22
    @3
    @20
    @15
    @1
    @0
    @20
    @15
    wb
    #
    @2
    @20
    @1
    @15
    cP
    @5
    cX
    cX
    opelxp
    baib
    #
    3ad2ant2
    biimpd
    adantrd
    @3
    @16
    @15
    @3
    @15
    @7
    simprl
    ex
    @3
    @15
    @23
    @16
    wb
    @3
    @15
    wa
    #
    @20
    @15
    @22
    @7
    @27
    @1
    @25
    @0
    @1
    @2
    @15
    simpl2
    #
    @26
    syl
    @22
    @6
    @9
    wcel
    #
    @27
    @7
    @6
    @21
    @9
    cP
    @5
    cD
    df-ov
    eleq1i
    @27
    @29
    @6
    cxr
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @7
    w3a
    #
    @7
    @27
    cc0
    cxr
    wcel
    @12
    @29
    @32
    wb
    0xr
    @27
    cR
    @0
    @1
    @2
    @15
    simpl3
    rpxrd
    cc0
    cR
    @6
    elico1
    sylancr
    @27
    @7
    @30
    @31
    wa
    #
    @7
    wa
    @32
    @27
    @33
    @7
    @27
    @30
    @31
    @27
    @0
    @1
    @15
    @30
    @0
    @1
    @2
    @15
    simpl1
    #
    @28
    @3
    @15
    simpr
    #
    cP
    @5
    cD
    cX
    psmetcl
    syl3anc
    @27
    @0
    @1
    @15
    @31
    @34
    @28
    @35
    cP
    @5
    cD
    cX
    psmetge0
    syl3anc
    jca
    biantrurd
    @30
    @31
    @7
    df-3an
    syl6rbbr
    bitrd
    syl5bbr
    anbi12d
    ex
    pm5.21ndd
    bitrd
    @1
    @0
    @17
    @14
    wb
    #
    @2
    @1
    @5
    cvv
    wcel
    @36
    vx
    vex
    @10
    cP
    @5
    cX
    cvv
    elimasng
    mpan2
    3ad2ant2
    @18
    @16
    wb
    @3
    @7
    vx
    cX
    rabid
    a1i
    3bitr4d
    eqrd
    eqtr4d
end
