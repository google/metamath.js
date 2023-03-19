include "cc.mm"
include "ce.mm"
include "clog.mm"
include "cima.mm"
include "cres.mm"
include "ccnv.mm"
include "cdv.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wtru.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "crest.mm"
include "ctop.mm"
include "wcel.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cr.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "logdmopn.mm"
include "wf1o.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "crn.mm"
include "wf1.mm"
include "wss.mm"
include "logf1o.mm"
include "f1of1.mm"
include "logdmss.mm"
include "f1ores.mm"
include "mp2an.mm"
include "f1ocnv.mm"
include "wb.mm"
include "cim.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "df-log.mm"
include "reseq1i.mm"
include "cnveqi.mm"
include "wf.mm"
include "wfun.mm"
include "eff.mm"
include "cdm.mm"
include "cnvimass.mm"
include "imf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "fssres.mm"
include "ffun.mm"
include "funcnvres2.mm"
include "mp2b.mm"
include "resabs1.mm"
include "3eqtri.mm"
include "imaeq1i.mm"
include "reseq2i.mm"
include "eqtr4i.mm"
include "f1oeq1.mm"
include "mpbi.mm"
include "ccncf.mm"
include "wrel.mm"
include "relres.mm"
include "dfrel2.mm"
include "eqtr3i.mm"
include "f1of.mm"
include "mp1i.mm"
include "imassrn.mm"
include "logrncn.mm"
include "ssriv.mm"
include "sstri.mm"
include "logcn.mm"
include "cncffvrn.mm"
include "sylibr.mm"
include "syl5eqel.mm"
include "cin.mm"
include "cnt.mm"
include "ssid.mm"
include "dvres.mm"
include "mp4an.mm"
include "dvef.mm"
include "dvloglem.mm"
include "isopn3i.mm"
include "reseq12i.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmres.mm"
include "sseqtr4i.mm"
include "df-ss.mm"
include "wn.mm"
include "wne.mm"
include "neirr.mm"
include "wa.mm"
include "resss.mm"
include "eqsstri.mm"
include "rnss.mm"
include "eff2.mm"
include "frn.mm"
include "sseli.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "mto.mm"
include "dvcnv.mm"
include "trud.mm"
include "oveq2i.mm"
include "fveq1i.mm"
include "f1ocnvfv2.mm"
include "mpan.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"
include "3eqtr3i.mm"

theorem dvlog
  let vx: setvar x
  let cD: class D
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )

  disjoint D x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  assert |- ( CC _D ( log |` D ) ) = ( x e. D |-> ( 1 / x ) )

  proof
    cc
    ce
    clog
    cD
    cima
    #
    cres
    #
    ccnv
    #
    cdv
    co
    #
    vx
    cD
    c1
    vx
    cv
    #
    @2
    cfv
    #
    cc
    @1
    cdv
    co
    #
    cfv
    #
    cdiv
    co
    #
    cmpt
    #
    cc
    clog
    cD
    cres
    #
    cdv
    co
    vx
    cD
    c1
    @4
    cdiv
    co
    #
    cmpt
    @3
    @9
    wceq
    wtru
    vx
    cc
    @1
    ccnfld
    ctopn
    cfv
    #
    @12
    @0
    cD
    @12
    eqid
    #
    @12
    cc
    crest
    co
    #
    @12
    @12
    ctop
    wcel
    #
    @14
    @12
    wceq
    @12
    @13
    cnfldtop
    #
    @12
    ctop
    cc
    cc
    @12
    @12
    @13
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    #
    cc
    cr
    cc
    cpr
    wcel
    wtru
    cnelprrecn
    a1i
    cD
    @12
    wcel
    wtru
    cD
    logcn.d
    logdmopn
    a1i
    @0
    cD
    @1
    wf1o
    #
    wtru
    @0
    cD
    @10
    ccnv
    #
    wf1o
    #
    @18
    cD
    @0
    @10
    wf1o
    #
    @20
    cc
    cc0
    csn
    cdif
    #
    clog
    crn
    #
    clog
    wf1
    #
    cD
    @22
    wss
    @21
    @22
    @23
    clog
    wf1o
    @24
    logf1o
    @22
    @23
    clog
    f1of1
    ax-mp
    cD
    logcn.d
    logdmss
    @22
    @23
    cD
    clog
    f1ores
    mp2an
    #
    cD
    @0
    @10
    f1ocnv
    ax-mp
    @19
    @1
    wceq
    @20
    @18
    wb
    @19
    ce
    ce
    cim
    ccnv
    cpi
    cneg
    cpi
    cioc
    co
    #
    cima
    #
    cres
    #
    ccnv
    #
    cD
    cima
    #
    cres
    #
    @1
    @19
    @29
    cD
    cres
    #
    ccnv
    #
    @28
    @30
    cres
    #
    @31
    @10
    @32
    clog
    @29
    cD
    df-log
    reseq1i
    cnveqi
    @27
    cc
    @28
    wf
    #
    @28
    wfun
    @33
    @34
    wceq
    cc
    cc
    ce
    wf
    #
    @27
    cc
    wss
    @35
    eff
    @27
    cim
    cdm
    cc
    cim
    @26
    cnvimass
    cc
    cr
    cim
    imf
    fdmi
    sseqtri
    cc
    cc
    @27
    ce
    fssres
    mp2an
    #
    @27
    cc
    @28
    ffun
    cD
    @28
    funcnvres2
    mp2b
    @30
    @27
    wss
    @34
    @31
    wceq
    @30
    @28
    cdm
    @27
    @28
    cD
    cnvimass
    @27
    cc
    @28
    @37
    fdmi
    sseqtri
    ce
    @30
    @27
    resabs1
    ax-mp
    3eqtri
    @0
    @30
    ce
    clog
    @29
    cD
    df-log
    imaeq1i
    reseq2i
    eqtr4i
    #
    @0
    cD
    @19
    @1
    f1oeq1
    ax-mp
    mpbi
    #
    a1i
    wtru
    @2
    @10
    cD
    @0
    ccncf
    co
    #
    @19
    ccnv
    #
    @2
    @10
    @19
    @1
    @38
    cnveqi
    @10
    wrel
    @41
    @10
    wceq
    clog
    cD
    relres
    @10
    dfrel2
    mpbi
    eqtr3i
    #
    wtru
    cD
    @0
    @10
    wf
    #
    @10
    @40
    wcel
    #
    @21
    @43
    wtru
    @25
    cD
    @0
    @10
    f1of
    mp1i
    @0
    cc
    wss
    #
    @10
    cD
    cc
    ccncf
    co
    wcel
    @44
    @43
    wb
    @0
    @23
    cc
    clog
    cD
    imassrn
    vx
    @23
    cc
    @4
    logrncn
    ssriv
    sstri
    #
    cD
    logcn.d
    logcn
    cD
    cc
    @0
    @10
    cncffvrn
    mp2an
    sylibr
    syl5eqel
    @6
    cdm
    #
    @0
    wceq
    wtru
    @47
    @1
    cdm
    @0
    ce
    cdm
    #
    cin
    #
    @0
    @6
    @1
    @6
    cc
    ce
    cdv
    co
    #
    @0
    @12
    cnt
    cfv
    cfv
    #
    cres
    #
    @1
    cc
    cc
    wss
    #
    @36
    @53
    @45
    @6
    @52
    wceq
    cc
    ssid
    #
    eff
    @54
    @46
    cc
    @0
    cc
    @12
    ce
    @12
    @13
    @17
    dvres
    mp4an
    #
    @50
    ce
    @51
    @0
    dvef
    @15
    @0
    @12
    wcel
    @51
    @0
    wceq
    @16
    cD
    logcn.d
    dvloglem
    @0
    @12
    isopn3i
    mp2an
    reseq12i
    eqtri
    #
    dmeqi
    ce
    @0
    dmres
    @0
    @48
    wss
    @49
    @0
    wceq
    @0
    cc
    @48
    @46
    cc
    cc
    ce
    eff
    fdmi
    sseqtr4i
    @0
    @48
    df-ss
    mpbi
    3eqtri
    a1i
    cc0
    @6
    crn
    #
    wcel
    #
    wn
    wtru
    @58
    cc0
    cc0
    wne
    #
    cc0
    neirr
    @58
    cc0
    cc
    wcel
    #
    @59
    @58
    cc0
    @22
    wcel
    @60
    @59
    wa
    @57
    @22
    cc0
    @57
    ce
    crn
    #
    @22
    @6
    ce
    wss
    @57
    @61
    wss
    @6
    @50
    ce
    @6
    @52
    @50
    @55
    @50
    @51
    resss
    eqsstri
    dvef
    sseqtri
    @6
    ce
    rnss
    ax-mp
    cc
    @22
    ce
    wf
    @61
    @22
    wss
    eff2
    cc
    @22
    ce
    frn
    ax-mp
    sstri
    sseli
    cc0
    cc
    cc0
    eldifsn
    sylib
    simprd
    mto
    a1i
    dvcnv
    trud
    @2
    @10
    cc
    cdv
    @42
    oveq2i
    vx
    cD
    @8
    @11
    @4
    cD
    wcel
    #
    @7
    @4
    c1
    cdiv
    @62
    @7
    @5
    @1
    cfv
    #
    @4
    @5
    @6
    @1
    @56
    fveq1i
    @18
    @62
    @63
    @4
    wceq
    @39
    @0
    cD
    @4
    @1
    f1ocnvfv2
    mpan
    syl5eq
    oveq2d
    mpteq2ia
    3eqtr3i
end
