include "wcel.mm"
include "wiso.mm"
include "w3a.mm"
include "cordt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "csn.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "wral.mm"
include "wf1o.mm"
include "isof1o.mm"
include "3ad2ant3.mm"
include "f1of.mm"
include "syl.mm"
include "wceq.mm"
include "fimacnv.mm"
include "ctopon.mm"
include "ordttopon.mm"
include "3ad2ant1.mm"
include "toponmax.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "imaeq2d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "f1odm.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wfn.mm"
include "wb.mm"
include "ad2antrr.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "simpr.mm"
include "biantrurd.mm"
include "ffvelrnda.mm"
include "breq1.mm"
include "notbid.mm"
include "elrab3.mm"
include "simpll3.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "isorel.mm"
include "syl12anc.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "breq2d.mm"
include "bitrd.mm"
include "bitr4d.mm"
include "3bitr2d.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"
include "simpl1.mm"
include "ordtopn1.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "3ad2ant2.mm"
include "rabexg.mm"
include "ralrimivw.mm"
include "eqid.mm"
include "imaeq2.mm"
include "ralrnmpt.mm"
include "mpbird.mm"
include "breq2.mm"
include "breq1d.mm"
include "ordtopn2.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "cuni.mm"
include "ordtuni.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "cfi.mm"
include "ctg.mm"
include "ordtval.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem ordthmeolem
  let cR: class R
  let cS: class S
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ordthmeo.1: |- X = dom R
  assume ordthmeo.2: |- Y = dom S


  assert |- ( ( R e. V /\ S e. W /\ F Isom R , S ( X , Y ) ) -> F e. ( ( ordTop ` R ) Cn ( ordTop ` S ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    cX
    cY
    cR
    cS
    cF
    wiso
    #
    w3a
    #
    cF
    cR
    cordt
    cfv
    #
    cS
    cordt
    cfv
    #
    ccn
    co
    wcel
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vz
    cv
    #
    cima
    #
    @4
    wcel
    #
    vz
    cY
    csn
    #
    vx
    cY
    vy
    cv
    #
    vx
    cv
    #
    cS
    wbr
    #
    wn
    #
    vy
    cY
    crab
    #
    cmpt
    #
    crn
    #
    vx
    cY
    @13
    @12
    cS
    wbr
    #
    wn
    #
    vy
    cY
    crab
    #
    cmpt
    #
    crn
    #
    cun
    #
    cun
    #
    wral
    #
    @3
    cX
    cY
    cF
    wf1o
    #
    @6
    @2
    @0
    @27
    @1
    cX
    cY
    cR
    cS
    cF
    isof1o
    3ad2ant3
    #
    cX
    cY
    cF
    f1of
    syl
    #
    @3
    @10
    vz
    @11
    wral
    @10
    vz
    @24
    wral
    #
    @26
    @3
    @10
    vz
    @11
    @3
    @10
    @8
    @11
    wcel
    #
    @7
    cY
    cima
    #
    @4
    wcel
    @3
    @32
    cX
    @4
    @3
    @6
    @32
    cX
    wceq
    @29
    cX
    cY
    cF
    fimacnv
    syl
    @3
    @4
    cX
    ctopon
    cfv
    wcel
    #
    cX
    @4
    wcel
    @0
    @1
    @33
    @2
    cR
    cV
    cX
    ordthmeo.1
    ordttopon
    3ad2ant1
    #
    cX
    @4
    toponmax
    syl
    eqeltrd
    @31
    @9
    @32
    @4
    @31
    @8
    cY
    @7
    @8
    cY
    elsni
    imaeq2d
    eleq1d
    syl5ibrcom
    ralrimiv
    @3
    @10
    vz
    @18
    wral
    #
    @10
    vz
    @23
    wral
    #
    @30
    @3
    @35
    @7
    @16
    cima
    #
    @4
    wcel
    #
    vx
    cY
    wral
    #
    @3
    @38
    vx
    cY
    @3
    @13
    cY
    wcel
    #
    wa
    #
    @37
    @8
    @13
    @7
    cfv
    #
    cR
    wbr
    #
    wn
    #
    vz
    cX
    crab
    #
    @4
    @41
    cX
    @37
    cin
    #
    @37
    @45
    @41
    @37
    cX
    wss
    @46
    @37
    wceq
    @41
    cF
    cdm
    #
    @37
    cX
    cF
    @16
    cnvimass
    @3
    @47
    cX
    wceq
    #
    @40
    @3
    @27
    @48
    @28
    cX
    cY
    cF
    f1odm
    syl
    adantr
    #
    syl5sseq
    @37
    cX
    sseqin2
    sylib
    @41
    @44
    vz
    cX
    @37
    @41
    @8
    cX
    wcel
    #
    wa
    #
    @8
    @37
    wcel
    #
    @50
    @8
    cF
    cfv
    #
    @16
    wcel
    #
    wa
    #
    @54
    @44
    @51
    cF
    cX
    wfn
    #
    @52
    @55
    wb
    @51
    @27
    @56
    @3
    @27
    @40
    @50
    @28
    ad2antrr
    cX
    cY
    cF
    f1ofn
    syl
    #
    cX
    @8
    @16
    cF
    elpreima
    syl
    @51
    @50
    @54
    @41
    @50
    simpr
    #
    biantrurd
    @51
    @54
    @53
    @13
    cS
    wbr
    #
    wn
    #
    @44
    @51
    @53
    cY
    wcel
    #
    @54
    @60
    wb
    @41
    cX
    cY
    @8
    cF
    @3
    @6
    @40
    @29
    adantr
    ffvelrnda
    #
    @15
    @60
    vy
    @53
    cY
    @12
    @53
    wceq
    #
    @14
    @59
    @12
    @53
    @13
    cS
    breq1
    notbid
    elrab3
    syl
    @51
    @43
    @59
    @51
    @43
    @53
    @42
    cF
    cfv
    #
    cS
    wbr
    #
    @59
    @51
    @2
    @50
    @42
    cX
    wcel
    #
    @43
    @65
    wb
    @0
    @1
    @2
    @40
    @50
    simpll3
    #
    @58
    @41
    @66
    @50
    @3
    cY
    cX
    @13
    @7
    @3
    @27
    cY
    cX
    @7
    wf1o
    cY
    cX
    @7
    wf
    @28
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @7
    f1of
    3syl
    ffvelrnda
    #
    adantr
    #
    cX
    cY
    @8
    @42
    cR
    cS
    cF
    isorel
    syl12anc
    @51
    @64
    @13
    @53
    cS
    @41
    @64
    @13
    wceq
    #
    @50
    @3
    @27
    @40
    @70
    @28
    cX
    cY
    @13
    cF
    f1ocnvfv2
    sylan
    adantr
    #
    breq2d
    bitrd
    notbid
    bitr4d
    3bitr2d
    rabbi2dva
    eqtr3d
    @41
    @0
    @66
    @45
    @4
    wcel
    @0
    @1
    @2
    @40
    simpl1
    #
    @68
    vz
    @42
    cR
    cV
    cX
    ordthmeo.1
    ordtopn1
    syl2anc
    eqeltrd
    ralrimiva
    @3
    @16
    cvv
    wcel
    #
    vx
    cY
    wral
    @35
    @39
    wb
    @3
    @73
    vx
    cY
    @3
    cY
    cvv
    wcel
    #
    @73
    @1
    @0
    @74
    @2
    @1
    cY
    cS
    cdm
    cvv
    ordthmeo.2
    cS
    cW
    dmexg
    syl5eqel
    #
    3ad2ant2
    #
    @15
    vy
    cY
    cvv
    rabexg
    syl
    ralrimivw
    @10
    @38
    vx
    vz
    cY
    @16
    @17
    cvv
    @17
    eqid
    @8
    @16
    wceq
    @9
    @37
    @4
    @8
    @16
    @7
    imaeq2
    eleq1d
    ralrnmpt
    syl
    mpbird
    @3
    @36
    @7
    @21
    cima
    #
    @4
    wcel
    #
    vx
    cY
    wral
    #
    @3
    @78
    vx
    cY
    @41
    @77
    @42
    @8
    cR
    wbr
    #
    wn
    #
    vz
    cX
    crab
    #
    @4
    @41
    cX
    @77
    cin
    #
    @77
    @82
    @41
    @77
    cX
    wss
    @83
    @77
    wceq
    @41
    @47
    @77
    cX
    cF
    @21
    cnvimass
    @49
    syl5sseq
    @77
    cX
    sseqin2
    sylib
    @41
    @81
    vz
    cX
    @77
    @51
    @8
    @77
    wcel
    #
    @50
    @53
    @21
    wcel
    #
    wa
    #
    @85
    @81
    @51
    @56
    @84
    @86
    wb
    @57
    cX
    @8
    @21
    cF
    elpreima
    syl
    @51
    @50
    @85
    @58
    biantrurd
    @51
    @85
    @13
    @53
    cS
    wbr
    #
    wn
    #
    @81
    @51
    @61
    @85
    @88
    wb
    @62
    @20
    @88
    vy
    @53
    cY
    @63
    @19
    @87
    @12
    @53
    @13
    cS
    breq2
    notbid
    elrab3
    syl
    @51
    @80
    @87
    @51
    @80
    @64
    @53
    cS
    wbr
    #
    @87
    @51
    @2
    @66
    @50
    @80
    @89
    wb
    @67
    @69
    @58
    cX
    cY
    @42
    @8
    cR
    cS
    cF
    isorel
    syl12anc
    @51
    @64
    @13
    @53
    cS
    @71
    breq1d
    bitrd
    notbid
    bitr4d
    3bitr2d
    rabbi2dva
    eqtr3d
    @41
    @0
    @66
    @82
    @4
    wcel
    @72
    @68
    vz
    @42
    cR
    cV
    cX
    ordthmeo.1
    ordtopn2
    syl2anc
    eqeltrd
    ralrimiva
    @3
    @21
    cvv
    wcel
    #
    vx
    cY
    wral
    @36
    @79
    wb
    @3
    @90
    vx
    cY
    @3
    @74
    @90
    @76
    @20
    vy
    cY
    cvv
    rabexg
    syl
    ralrimivw
    @10
    @78
    vx
    vz
    cY
    @21
    @22
    cvv
    @22
    eqid
    @8
    @21
    wceq
    @9
    @77
    @4
    @8
    @21
    @7
    imaeq2
    eleq1d
    ralrnmpt
    syl
    mpbird
    @10
    vz
    @18
    @23
    ralunb
    sylanbrc
    @10
    vz
    @11
    @24
    ralunb
    sylanbrc
    @3
    vz
    @25
    cF
    @4
    @5
    cvv
    cX
    cY
    @34
    @1
    @0
    @25
    cvv
    wcel
    #
    @2
    @1
    @25
    cuni
    #
    cvv
    wcel
    @91
    @1
    cY
    @92
    cvv
    vx
    vy
    @18
    @23
    cS
    cW
    cY
    ordthmeo.2
    @18
    eqid
    #
    @23
    eqid
    #
    ordtuni
    @75
    eqeltrrd
    @25
    uniexb
    sylibr
    3ad2ant2
    @1
    @0
    @5
    @25
    cfi
    cfv
    ctg
    cfv
    wceq
    @2
    vx
    vy
    @18
    @23
    cS
    cW
    cY
    ordthmeo.2
    @93
    @94
    ordtval
    3ad2ant2
    @1
    @0
    @5
    cY
    ctopon
    cfv
    wcel
    @2
    cS
    cW
    cY
    ordthmeo.2
    ordttopon
    3ad2ant2
    subbascn
    mpbir2and
end
