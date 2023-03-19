include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cv.mm"
include "ccnv.mm"
include "c1o.mm"
include "csn.mm"
include "cima.mm"
include "wel.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wa.mm"
include "vex.mm"
include "cnvex.mm"
include "imaexg.mm"
include "mp1i.mm"
include "mptexg.mm"
include "adantr.mm"
include "wceq.mm"
include "wss.mm"
include "wf.mm"
include "con0.mm"
include "wb.mm"
include "2on.mm"
include "elmapg.mm"
include "mpan.mm"
include "anbi1d.mm"
include "wral.mm"
include "csuc.mm"
include "1on.mm"
include "elexi.mm"
include "sucid.mm"
include "df-2o.mm"
include "eleqtrri.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o2.mm"
include "keepel.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "simpr.mm"
include "feq1d.mm"
include "mpbiri.mm"
include "cfv.mm"
include "fveq1d.mm"
include "elequ1.mm"
include "ifbid.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "eqeq1d.mm"
include "iftrue.mm"
include "wn.mm"
include "noel.mm"
include "iffalse.mm"
include "0lt1o.mm"
include "eleq2.mm"
include "syl6bi.mm"
include "mtoi.mm"
include "con4i.mm"
include "impbii.mm"
include "syl6rbbr.mm"
include "fvex.mm"
include "elsn.mm"
include "syl6bbr.mm"
include "pm5.32da.mm"
include "wi.mm"
include "ssel.mm"
include "pm4.71rd.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "3bitr4d.mm"
include "eqrdv.mm"
include "jca.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "eqsstrd.mm"
include "simplr.mm"
include "eleq2d.mm"
include "wbr.mm"
include "fnbrfvb.mm"
include "sylan.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "bitr4d.mm"
include "biimpa.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wo.mm"
include "ffvelrn.mm"
include "adantlr.mm"
include "df2o3.mm"
include "syl6eleq.mm"
include "elpr.mm"
include "sylib.mm"
include "ord.mm"
include "sylibrd.mm"
include "con1d.mm"
include "imp.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbird.mm"
include "selpw.mm"
include "anbi1i.mm"
include "f1ocnvd.mm"

theorem pw2f1ocnv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let cV: class V
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume pw2f1o2.f: |- F = ( x e. ( 2o ^m A ) |-> ( `' x " { 1o } ) )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V x
  disjoint V y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( A e. V -> ( F : ( 2o ^m A ) -1-1-onto-> ~P A /\ `' F = ( y e. ~P A |-> ( z e. A |-> if ( z e. y , 1o , (/) ) ) ) ) )

  proof
    cA
    cV
    wcel
    #
    vx
    vy
    c2o
    cA
    cmap
    co
    #
    cA
    cpw
    #
    vx
    cv
    #
    ccnv
    #
    c1o
    csn
    #
    cima
    #
    vz
    cA
    vz
    vy
    wel
    #
    c1o
    c0
    cif
    #
    cmpt
    #
    cF
    cvv
    cvv
    pw2f1o2.f
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    @0
    @3
    @1
    wcel
    #
    wa
    @3
    vx
    vex
    cnvex
    @4
    @5
    cvv
    imaexg
    mp1i
    @0
    @9
    cvv
    wcel
    vy
    cv
    #
    @2
    wcel
    #
    vz
    cA
    @8
    cV
    mptexg
    adantr
    @0
    @10
    @11
    @6
    wceq
    #
    wa
    #
    @11
    cA
    wss
    #
    @3
    @9
    wceq
    #
    wa
    #
    @12
    @16
    wa
    @0
    @14
    cA
    c2o
    @3
    wf
    #
    @13
    wa
    #
    @17
    @0
    @10
    @18
    @13
    c2o
    con0
    wcel
    @0
    @10
    @18
    wb
    2on
    c2o
    cA
    @3
    con0
    cV
    elmapg
    mpan
    anbi1d
    @17
    @19
    @17
    @18
    @13
    @17
    @18
    cA
    c2o
    @9
    wf
    #
    @8
    c2o
    wcel
    #
    vz
    cA
    wral
    @20
    @21
    vz
    cA
    @7
    c1o
    c0
    c2o
    c1o
    c1o
    csuc
    c2o
    c1o
    c1o
    con0
    1on
    elexi
    #
    sucid
    df-2o
    eleqtrri
    c0
    c0
    c0
    csn
    #
    cpr
    c2o
    c0
    @23
    0ex
    prid1
    df2o2
    eleqtrri
    keepel
    rgenw
    vz
    cA
    c2o
    @8
    @9
    @9
    eqid
    #
    fmpt
    mpbi
    #
    @17
    cA
    c2o
    @3
    @9
    @15
    @16
    simpr
    #
    feq1d
    mpbiri
    #
    @17
    vw
    @11
    @6
    @17
    vw
    cv
    #
    cA
    wcel
    #
    vw
    vy
    wel
    #
    wa
    @29
    @28
    @3
    cfv
    #
    @5
    wcel
    #
    wa
    #
    @30
    @28
    @6
    wcel
    #
    @17
    @29
    @30
    @32
    @17
    @29
    wa
    #
    @30
    @31
    c1o
    wceq
    #
    @32
    @35
    @36
    @30
    c1o
    c0
    cif
    #
    c1o
    wceq
    #
    @30
    @35
    @31
    @37
    c1o
    @17
    @29
    @31
    @28
    @9
    cfv
    #
    @37
    @17
    @28
    @3
    @9
    @26
    fveq1d
    vz
    @28
    @8
    @37
    cA
    @9
    vz
    cv
    @28
    wceq
    @7
    @30
    c1o
    c0
    vz
    vw
    vy
    elequ1
    ifbid
    @24
    @30
    c1o
    c0
    cvv
    @22
    0ex
    keepel
    fvmpt
    #
    sylan9eq
    eqeq1d
    @30
    @38
    @30
    c1o
    c0
    iftrue
    #
    @30
    @38
    @30
    wn
    #
    @38
    c0
    c0
    wcel
    #
    c0
    noel
    @42
    @38
    c0
    c1o
    wceq
    #
    @43
    @42
    @37
    c0
    c1o
    @30
    c1o
    c0
    iffalse
    #
    eqeq1d
    @44
    @43
    c0
    c1o
    wcel
    0lt1o
    c0
    c1o
    c0
    eleq2
    mpbiri
    syl6bi
    mtoi
    con4i
    impbii
    syl6rbbr
    @31
    c1o
    @28
    @3
    fvex
    #
    elsn
    syl6bbr
    pm5.32da
    @17
    @30
    @29
    @15
    @30
    @29
    wi
    @16
    @11
    cA
    @28
    ssel
    adantr
    pm4.71rd
    @17
    @18
    @3
    cA
    wfn
    #
    @34
    @33
    wb
    @27
    cA
    c2o
    @3
    ffn
    #
    cA
    @28
    @5
    @3
    elpreima
    3syl
    3bitr4d
    eqrdv
    jca
    @19
    @15
    @16
    @19
    @11
    @6
    cA
    @18
    @13
    simpr
    @19
    @3
    cdm
    #
    @6
    cA
    @3
    @5
    cnvimass
    @18
    @49
    cA
    wceq
    @13
    cA
    c2o
    @3
    fdm
    adantr
    syl5sseq
    eqsstrd
    @19
    @16
    @31
    @39
    wceq
    #
    vw
    cA
    wral
    #
    @19
    @50
    vw
    cA
    @19
    @29
    wa
    #
    @31
    @37
    @39
    @52
    @30
    @31
    @37
    wceq
    @52
    @30
    wa
    @31
    c1o
    @37
    @52
    @30
    @36
    @52
    @30
    @34
    @36
    @52
    @11
    @6
    @28
    @18
    @13
    @29
    simplr
    eleq2d
    @52
    @36
    @28
    c1o
    @3
    wbr
    #
    @34
    @19
    @47
    @29
    @36
    @53
    wb
    @18
    @47
    @13
    @48
    adantr
    #
    cA
    @28
    c1o
    @3
    fnbrfvb
    sylan
    c1o
    con0
    wcel
    @34
    @53
    wb
    1on
    @3
    c1o
    @28
    con0
    vw
    vex
    eliniseg
    ax-mp
    syl6bbr
    bitr4d
    #
    biimpa
    @30
    @38
    @52
    @41
    adantl
    eqtr4d
    @52
    @42
    wa
    @31
    c0
    @37
    @52
    @42
    @31
    c0
    wceq
    #
    @52
    @56
    @30
    @52
    @56
    wn
    @36
    @30
    @52
    @56
    @36
    @52
    @31
    c0
    c1o
    cpr
    #
    wcel
    @56
    @36
    wo
    @52
    @31
    c2o
    @57
    @18
    @29
    @31
    c2o
    wcel
    @13
    cA
    c2o
    @28
    @3
    ffvelrn
    adantlr
    df2o3
    syl6eleq
    @31
    c0
    c1o
    @46
    elpr
    sylib
    ord
    @55
    sylibrd
    con1d
    imp
    @42
    @37
    c0
    wceq
    @52
    @45
    adantl
    eqtr4d
    pm2.61dan
    @29
    @39
    @37
    wceq
    @19
    @40
    adantl
    eqtr4d
    ralrimiva
    @19
    @47
    @9
    cA
    wfn
    #
    @16
    @51
    wb
    @54
    @20
    @58
    @25
    cA
    c2o
    @9
    ffn
    ax-mp
    vw
    cA
    @3
    @9
    eqfnfv
    sylancl
    mpbird
    jca
    impbii
    syl6bbr
    @12
    @15
    @16
    vy
    cA
    selpw
    anbi1i
    syl6bbr
    f1ocnvd
end
