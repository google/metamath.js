include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cvtx.mm"
include "wral.mm"
include "cusgr.mm"
include "crab.mm"
include "cvv.mm"
include "wnel.mm"
include "ciedg.mm"
include "c0.mm"
include "wf.mm"
include "copab.mm"
include "wss.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "elopab.mm"
include "f0bi.mm"
include "opeq2.mm"
include "vex.mm"
include "usgr0eop.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "opiedgfv.mm"
include "mp2an.mm"
include "id.mm"
include "syl5eq.mm"
include "jca.mm"
include "sylbi.mm"
include "adantl.mm"
include "wb.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "elrab.mm"
include "sylibr.mm"
include "exlimivv.mm"
include "ssriv.mm"
include "eqid.mm"
include "griedg0prc.mm"
include "prcssprc.mm"
include "crusgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "w3a.mm"
include "df-3an.mm"
include "bicomi.mm"
include "a1i.mm"
include "0xnn0.mm"
include "ibar.mm"
include "mpan2.mm"
include "isrusgr0.mm"
include "3bitr4d.mm"
include "rabbiia.mm"
include "cedg.mm"
include "usgr0edg0rusgr.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "uhgriedg0edg0.mm"
include "syl.mm"
include "bitrd.mm"
include "eqtri.mm"
include "neleq1.mm"
include "mpbir.mm"

theorem rgrusgrprc
  let vv: setvar v
  let vg: setvar g
  let ve: setvar e
  let vp: setvar p

  disjoint g v
  disjoint e g
  disjoint e p
  disjoint e v
  disjoint g p
  disjoint p v
  assert |- { g e. USGraph | A. v e. ( Vtx ` g ) ( ( VtxDeg ` g ) ` v ) = 0 } e/ _V

  proof
    vv
    cv
    #
    vg
    cv
    #
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    vv
    @1
    cvtx
    cfv
    #
    wral
    #
    vg
    cusgr
    crab
    #
    cvv
    wnel
    #
    @1
    ciedg
    cfv
    #
    c0
    wceq
    #
    vg
    cusgr
    crab
    #
    cvv
    wnel
    #
    c0
    c0
    ve
    cv
    #
    wf
    #
    vv
    ve
    copab
    #
    @9
    wss
    @13
    cvv
    wnel
    @10
    vp
    @13
    @9
    vp
    cv
    #
    @13
    wcel
    @14
    @0
    @11
    cop
    #
    wceq
    #
    @12
    wa
    #
    ve
    wex
    vv
    wex
    @14
    @9
    wcel
    #
    @12
    vv
    ve
    @14
    elopab
    @17
    @18
    vv
    ve
    @17
    @14
    cusgr
    wcel
    #
    @14
    ciedg
    cfv
    #
    c0
    wceq
    #
    wa
    #
    @18
    @17
    @22
    @15
    cusgr
    wcel
    #
    @15
    ciedg
    cfv
    #
    c0
    wceq
    #
    wa
    #
    @12
    @26
    @16
    @12
    @11
    c0
    wceq
    #
    @26
    @11
    c0
    f0bi
    @27
    @23
    @25
    @27
    @15
    @0
    c0
    cop
    #
    cusgr
    @11
    c0
    @0
    opeq2
    @0
    cvv
    wcel
    #
    @28
    cusgr
    wcel
    vv
    vex
    #
    @0
    cvv
    usgr0eop
    ax-mp
    syl6eqel
    @27
    @24
    @11
    c0
    @29
    @11
    cvv
    wcel
    @24
    @11
    wceq
    @30
    ve
    vex
    @11
    @0
    cvv
    cvv
    opiedgfv
    mp2an
    @27
    id
    syl5eq
    jca
    sylbi
    adantl
    @16
    @22
    @26
    wb
    @12
    @16
    @19
    @23
    @21
    @25
    @14
    @15
    cusgr
    eleq1
    @16
    @20
    @24
    c0
    @14
    @15
    ciedg
    fveq2
    eqeq1d
    anbi12d
    adantr
    mpbird
    @8
    @21
    vg
    @14
    cusgr
    @1
    @14
    wceq
    @7
    @20
    c0
    @1
    @14
    ciedg
    fveq2
    eqeq1d
    elrab
    sylibr
    exlimivv
    sylbi
    ssriv
    vv
    @13
    ve
    @13
    eqid
    griedg0prc
    @13
    @9
    prcssprc
    mp2an
    @5
    @9
    wceq
    @6
    @10
    wb
    @5
    @1
    cc0
    crusgr
    wbr
    #
    vg
    cusgr
    crab
    @9
    @4
    @31
    vg
    cusgr
    @1
    cusgr
    wcel
    #
    @32
    cc0
    cxnn0
    wcel
    #
    wa
    #
    @4
    wa
    #
    @32
    @33
    @4
    w3a
    #
    @4
    @31
    @35
    @36
    wb
    @32
    @36
    @35
    @32
    @33
    @4
    df-3an
    bicomi
    a1i
    @32
    @33
    @4
    @35
    wb
    0xnn0
    @34
    @4
    ibar
    mpan2
    @32
    @33
    @31
    @36
    wb
    0xnn0
    vv
    @2
    @1
    cc0
    @3
    cusgr
    cxnn0
    @3
    eqid
    @2
    eqid
    isrusgr0
    mpan2
    3bitr4d
    rabbiia
    @31
    @8
    vg
    cusgr
    @32
    @31
    @1
    cedg
    cfv
    c0
    wceq
    #
    @8
    @1
    usgr0edg0rusgr
    @32
    @1
    cuhgr
    wcel
    @37
    @8
    wb
    @1
    usgruhgr
    @1
    uhgriedg0edg0
    syl
    bitrd
    rabbiia
    eqtri
    @5
    @9
    cvv
    neleq1
    ax-mp
    mpbir
end
