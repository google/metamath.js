include "co.mm"
include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "chom.mm"
include "cfv.mm"
include "cbs.mm"
include "cco.mm"
include "eqid.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "setcbas.mm"
include "eleqtrd.mm"
include "epihom.mm"
include "sselda.mm"
include "elsetchom.mm"
include "biimpa.mm"
include "syldan.mm"
include "wss.mm"
include "frn.mm"
include "cv.mm"
include "wral.mm"
include "c1o.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "c2o.mm"
include "ccom.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "iftrued.mm"
include "mpteq2dva.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "eleq1.mm"
include "ifbid.mm"
include "fmptco.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "3eqtr4d.mm"
include "adantr.mm"
include "cpr.mm"
include "com.mm"
include "1onn.mm"
include "elexi.mm"
include "prid2.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "0ex.mm"
include "prid1.mm"
include "keepel.mm"
include "fmpti.mm"
include "setcco.mm"
include "fconst6g.mm"
include "mp1i.mm"
include "simpr.mm"
include "mpbird.mm"
include "epii.mm"
include "mpbid.mm"
include "syl6eq.mm"
include "wb.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "sylib.mm"
include "wn.mm"
include "1n0.mm"
include "nesymi.mm"
include "iffalse.mm"
include "eqeq1d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "eqssd.mm"
include "dffo2.mm"
include "sylanbrc.mm"
include "wi.mm"
include "fof.mm"
include "adantl.mm"
include "biimpar.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "eqeq12d.mm"
include "simplr.mm"
include "cocan2.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "sylbid.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "ex.mm"
include "sylbird.mm"
include "ralrimiv.mm"
include "isepi2.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem setcepi
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cE: class E
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume setcmon.c: |- C = ( SetCat ` U )
  assume setcmon.u: |- ( ph -> U e. V )
  assume setcmon.x: |- ( ph -> X e. U )
  assume setcmon.y: |- ( ph -> Y e. U )
  assume setcepi.h: |- E = ( Epi ` C )
  assume setcepi.2: |- ( ph -> 2o e. U )


  assert |- ( ph -> ( F e. ( X E Y ) <-> F : X -onto-> Y ) )

  proof
    wph
    cF
    cX
    cY
    cE
    co
    #
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    wph
    @1
    wa
    #
    cX
    cY
    cF
    wf
    #
    cF
    crn
    #
    cY
    wceq
    @2
    wph
    @1
    cF
    cX
    cY
    cC
    chom
    cfv
    #
    co
    #
    wcel
    #
    @4
    wph
    @0
    @7
    cF
    wph
    cC
    cbs
    cfv
    #
    cC
    cC
    cco
    cfv
    #
    cE
    @6
    cX
    cY
    @9
    eqid
    #
    @6
    eqid
    #
    @10
    eqid
    #
    setcepi.h
    wph
    cU
    cV
    wcel
    #
    cC
    ccat
    wcel
    #
    setcmon.u
    cC
    cU
    cV
    setcmon.c
    setccat
    syl
    #
    wph
    cX
    cU
    @9
    setcmon.x
    wph
    cC
    cU
    cV
    setcmon.c
    setcmon.u
    setcbas
    #
    eleqtrd
    #
    wph
    cY
    cU
    @9
    setcmon.y
    @17
    eleqtrd
    #
    epihom
    sselda
    wph
    @8
    @4
    wph
    cC
    cU
    cF
    @6
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    @12
    setcmon.x
    setcmon.y
    elsetchom
    #
    biimpa
    syldan
    #
    @3
    @5
    cY
    @3
    @4
    @5
    cY
    wss
    @21
    cX
    cY
    cF
    frn
    syl
    @3
    va
    cv
    #
    @5
    wcel
    #
    va
    cY
    wral
    #
    cY
    @5
    wss
    @3
    @23
    c1o
    c0
    cif
    #
    c1o
    wceq
    #
    va
    cY
    wral
    #
    @24
    @3
    va
    cY
    @25
    cmpt
    #
    va
    cY
    c1o
    cmpt
    #
    wceq
    #
    @27
    @3
    @28
    cY
    c1o
    csn
    cxp
    #
    @29
    @3
    @28
    cF
    cX
    cY
    cop
    #
    c2o
    @10
    co
    #
    co
    #
    @31
    cF
    @33
    co
    #
    wceq
    @28
    @31
    wceq
    @3
    @28
    cF
    ccom
    #
    @31
    cF
    ccom
    #
    @34
    @35
    @3
    vx
    cX
    vx
    cv
    #
    cF
    cfv
    #
    @5
    wcel
    #
    c1o
    c0
    cif
    #
    cmpt
    vx
    cX
    c1o
    cmpt
    @36
    @37
    @3
    vx
    cX
    @41
    c1o
    @3
    @38
    cX
    wcel
    #
    wa
    @40
    c1o
    c0
    @3
    cF
    cX
    wfn
    #
    @42
    @40
    @3
    @4
    @43
    @21
    cX
    cY
    cF
    ffn
    syl
    cX
    @38
    cF
    fnfvelrn
    sylan
    iftrued
    mpteq2dva
    @3
    vx
    va
    cX
    cY
    @39
    @25
    @41
    cF
    @28
    @3
    cX
    cY
    @38
    cF
    @21
    ffvelrnda
    #
    @3
    vx
    cX
    cY
    cF
    @21
    feqmptd
    #
    @3
    @28
    eqidd
    @22
    @39
    wceq
    #
    @23
    @40
    c1o
    c0
    @22
    @39
    @5
    eleq1
    ifbid
    fmptco
    @3
    vx
    va
    cX
    cY
    @39
    c1o
    c1o
    cF
    @31
    @44
    @45
    @31
    @29
    wceq
    @3
    va
    cY
    c1o
    fconstmpt
    #
    a1i
    @46
    c1o
    eqidd
    fmptco
    3eqtr4d
    @3
    cC
    @10
    cU
    cF
    @28
    cV
    cX
    cY
    c2o
    setcmon.c
    wph
    @14
    @1
    setcmon.u
    adantr
    #
    @13
    wph
    cX
    cU
    wcel
    #
    @1
    setcmon.x
    adantr
    #
    wph
    cY
    cU
    wcel
    #
    @1
    setcmon.y
    adantr
    #
    wph
    c2o
    cU
    wcel
    @1
    setcepi.2
    adantr
    #
    @21
    cY
    c2o
    @28
    wf
    #
    @3
    va
    cY
    c2o
    @25
    @28
    @28
    eqid
    @25
    c2o
    wcel
    #
    @22
    cY
    wcel
    @23
    c1o
    c0
    c2o
    c1o
    c0
    c1o
    cpr
    #
    c2o
    c0
    c1o
    c1o
    com
    1onn
    elexi
    prid2
    df2o3
    eleqtrri
    #
    c0
    @56
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    keepel
    #
    a1i
    fmpti
    a1i
    #
    setcco
    @3
    cC
    @10
    cU
    cF
    @31
    cV
    cX
    cY
    c2o
    setcmon.c
    @48
    @13
    @50
    @52
    @53
    @21
    c1o
    c2o
    wcel
    cY
    c2o
    @31
    wf
    #
    @3
    @57
    cY
    c1o
    c2o
    fconst6g
    mp1i
    #
    setcco
    3eqtr4d
    @3
    @9
    cC
    @10
    cE
    cF
    @28
    @6
    @31
    cX
    cY
    c2o
    @11
    @12
    @13
    setcepi.h
    wph
    @15
    @1
    @16
    adantr
    wph
    cX
    @9
    wcel
    @1
    @18
    adantr
    wph
    cY
    @9
    wcel
    @1
    @19
    adantr
    wph
    c2o
    @9
    wcel
    @1
    wph
    c2o
    cU
    @9
    setcepi.2
    @17
    eleqtrd
    adantr
    wph
    @1
    simpr
    @3
    @28
    cY
    c2o
    @6
    co
    #
    wcel
    @54
    @59
    @3
    cC
    cU
    @28
    @6
    cV
    cY
    c2o
    setcmon.c
    @48
    @12
    @52
    @53
    elsetchom
    mpbird
    @3
    @31
    @62
    wcel
    @60
    @61
    @3
    cC
    cU
    @31
    @6
    cV
    cY
    c2o
    setcmon.c
    @48
    @12
    @52
    @53
    elsetchom
    mpbird
    epii
    mpbid
    @47
    syl6eq
    @55
    va
    cY
    wral
    @30
    @27
    wb
    @55
    va
    cY
    @58
    rgenw
    va
    cY
    @25
    c1o
    c2o
    mpteqb
    ax-mp
    sylib
    @26
    @23
    va
    cY
    @23
    @26
    @23
    wn
    #
    @26
    c0
    c1o
    wceq
    c1o
    c0
    1n0
    nesymi
    @63
    @25
    c0
    c1o
    @23
    c1o
    c0
    iffalse
    eqeq1d
    mtbiri
    con4i
    ralimi
    syl
    va
    cY
    @5
    dfss3
    sylibr
    eqssd
    cX
    cY
    cF
    dffo2
    sylanbrc
    wph
    @2
    wa
    #
    @1
    @8
    vg
    cv
    #
    cF
    @32
    vz
    cv
    #
    @10
    co
    #
    co
    #
    vh
    cv
    #
    cF
    @67
    co
    #
    wceq
    #
    @65
    @69
    wceq
    #
    wi
    #
    vh
    cY
    @66
    @6
    co
    #
    wral
    vg
    @74
    wral
    #
    vz
    @9
    wral
    #
    wph
    @2
    @4
    @8
    @2
    @4
    wph
    cX
    cY
    cF
    fof
    adantl
    #
    wph
    @8
    @4
    @20
    biimpar
    syldan
    @64
    @75
    vz
    @9
    @64
    @66
    @9
    wcel
    @66
    cU
    wcel
    #
    @75
    @64
    cU
    @9
    @66
    wph
    cU
    @9
    wceq
    @2
    @17
    adantr
    eleq2d
    @64
    @78
    @75
    @64
    @78
    wa
    @73
    vg
    vh
    @74
    @74
    @64
    @78
    @65
    @74
    wcel
    #
    @69
    @74
    wcel
    #
    wa
    #
    @73
    @64
    @78
    @81
    wa
    #
    wa
    #
    @71
    @65
    cF
    ccom
    #
    @69
    cF
    ccom
    #
    wceq
    #
    @72
    @83
    @68
    @84
    @70
    @85
    @83
    cC
    @10
    cU
    cF
    @65
    cV
    cX
    cY
    @66
    setcmon.c
    wph
    @14
    @2
    @82
    setcmon.u
    ad2antrr
    #
    @13
    wph
    @49
    @2
    @82
    setcmon.x
    ad2antrr
    #
    wph
    @51
    @2
    @82
    setcmon.y
    ad2antrr
    #
    @64
    @78
    @81
    simprl
    #
    @64
    @4
    @82
    @77
    adantr
    #
    @83
    @79
    cY
    @66
    @65
    wf
    #
    @64
    @78
    @79
    @80
    simprrl
    @83
    cC
    cU
    @65
    @6
    cV
    cY
    @66
    setcmon.c
    @87
    @12
    @89
    @90
    elsetchom
    mpbid
    #
    setcco
    @83
    cC
    @10
    cU
    cF
    @69
    cV
    cX
    cY
    @66
    setcmon.c
    @87
    @13
    @88
    @89
    @90
    @91
    @83
    @80
    cY
    @66
    @69
    wf
    #
    @64
    @78
    @79
    @80
    simprrr
    @83
    cC
    cU
    @69
    @6
    cV
    cY
    @66
    setcmon.c
    @87
    @12
    @89
    @90
    elsetchom
    mpbid
    #
    setcco
    eqeq12d
    @83
    @86
    @72
    @83
    @2
    @65
    cY
    wfn
    #
    @69
    cY
    wfn
    #
    @86
    @72
    wb
    wph
    @2
    @82
    simplr
    @83
    @92
    @96
    @93
    cY
    @66
    @65
    ffn
    syl
    @83
    @94
    @97
    @95
    cY
    @66
    @69
    ffn
    syl
    cX
    cY
    cF
    @65
    @69
    cocan2
    syl3anc
    biimpd
    sylbid
    anassrs
    ralrimivva
    ex
    sylbird
    ralrimiv
    wph
    @1
    @8
    @76
    wa
    wb
    @2
    wph
    vz
    @9
    cC
    @10
    vg
    vh
    cE
    cF
    @6
    cX
    cY
    @11
    @12
    @13
    setcepi.h
    @16
    @18
    @19
    isepi2
    adantr
    mpbir2and
    impbida
end
