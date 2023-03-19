include "co.mm"
include "wcel.mm"
include "wf1.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "chom.mm"
include "cbs.mm"
include "cco.mm"
include "eqid.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "setcbas.mm"
include "eleqtrd.mm"
include "monhom.mm"
include "sselda.mm"
include "elsetchom.mm"
include "biimpa.mm"
include "syldan.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "ccom.mm"
include "simprr.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "wfn.mm"
include "adantr.mm"
include "ffn.mm"
include "simprll.mm"
include "fcoconst.mm"
include "syl2anc.mm"
include "simprlr.mm"
include "3eqtr4d.mm"
include "ad2antrr.mm"
include "fconst6g.mm"
include "setcco.mm"
include "simplr.mm"
include "mpbird.mm"
include "moni.mm"
include "mpbid.mm"
include "fveq1d.mm"
include "vex.mm"
include "fvconst2.mm"
include "3eqtr3d.mm"
include "expr.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "f1f.mm"
include "biimpar.mm"
include "sylan2.mm"
include "eleq2d.mm"
include "simprl.mm"
include "simprrl.mm"
include "ad2antlr.mm"
include "simprrr.mm"
include "eqeq12d.mm"
include "wb.mm"
include "cocan1.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "sylbid.mm"
include "anassrs.mm"
include "ex.mm"
include "sylbird.mm"
include "ralrimiv.mm"
include "ismon2.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem setcmon
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cF: class F
  let cM: class M
  let cV: class V
  let cX: class X
  let cY: class Y
  let cE: class E
  let vx: setvar x
  let va: setvar a
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  assume setcmon.c: |- C = ( SetCat ` U )
  assume setcmon.u: |- ( ph -> U e. V )
  assume setcmon.x: |- ( ph -> X e. U )
  assume setcmon.y: |- ( ph -> Y e. U )
  assume setcmon.h: |- M = ( Mono ` C )


  assert |- ( ph -> ( F e. ( X M Y ) <-> F : X -1-1-> Y ) )

  proof
    wph
    cF
    cX
    cY
    cM
    co
    #
    wcel
    #
    cX
    cY
    cF
    wf1
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
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
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
    @13
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
    @12
    cM
    cX
    cY
    @15
    eqid
    #
    @12
    eqid
    #
    @16
    eqid
    #
    setcmon.h
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
    @15
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
    @15
    setcmon.y
    @23
    eleqtrd
    #
    monhom
    sselda
    wph
    @14
    @4
    wph
    cC
    cU
    cF
    @12
    cV
    cX
    cY
    setcmon.c
    setcmon.u
    @18
    setcmon.x
    setcmon.y
    elsetchom
    #
    biimpa
    syldan
    #
    @3
    @11
    vx
    vy
    cX
    cX
    @3
    @5
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    @9
    @10
    @3
    @30
    @9
    wa
    #
    wa
    #
    @5
    cX
    @5
    csn
    cxp
    #
    cfv
    #
    @5
    cX
    @7
    csn
    cxp
    #
    cfv
    #
    @5
    @7
    @32
    @5
    @33
    @35
    @32
    cF
    @33
    cX
    cX
    cop
    cY
    @16
    co
    #
    co
    #
    cF
    @35
    @37
    co
    #
    wceq
    @33
    @35
    wceq
    @32
    cF
    @33
    ccom
    #
    cF
    @35
    ccom
    #
    @38
    @39
    @32
    cX
    @6
    csn
    #
    cxp
    #
    cX
    @8
    csn
    #
    cxp
    #
    @40
    @41
    @32
    @42
    @44
    cX
    @32
    @6
    @8
    @3
    @30
    @9
    simprr
    sneqd
    xpeq2d
    @32
    cF
    cX
    wfn
    #
    @28
    @40
    @43
    wceq
    @32
    @4
    @46
    @3
    @4
    @31
    @27
    adantr
    #
    cX
    cY
    cF
    ffn
    syl
    #
    @3
    @28
    @29
    @9
    simprll
    #
    cF
    cX
    cX
    @5
    fcoconst
    syl2anc
    @32
    @46
    @29
    @41
    @45
    wceq
    @48
    @3
    @28
    @29
    @9
    simprlr
    #
    cF
    cX
    cX
    @7
    fcoconst
    syl2anc
    3eqtr4d
    @32
    cC
    @16
    cU
    @33
    cF
    cV
    cX
    cX
    cY
    setcmon.c
    wph
    @20
    @1
    @31
    setcmon.u
    ad2antrr
    #
    @19
    wph
    cX
    cU
    wcel
    #
    @1
    @31
    setcmon.x
    ad2antrr
    #
    @53
    wph
    cY
    cU
    wcel
    #
    @1
    @31
    setcmon.y
    ad2antrr
    #
    @32
    @28
    cX
    cX
    @33
    wf
    #
    @49
    cX
    @5
    cX
    fconst6g
    syl
    #
    @47
    setcco
    @32
    cC
    @16
    cU
    @35
    cF
    cV
    cX
    cX
    cY
    setcmon.c
    @51
    @19
    @53
    @53
    @55
    @32
    @29
    cX
    cX
    @35
    wf
    #
    @50
    cX
    @7
    cX
    fconst6g
    syl
    #
    @47
    setcco
    3eqtr4d
    @32
    @15
    cC
    @16
    cF
    @33
    @12
    @35
    cM
    cX
    cY
    cX
    @17
    @18
    @19
    setcmon.h
    wph
    @21
    @1
    @31
    @22
    ad2antrr
    wph
    cX
    @15
    wcel
    @1
    @31
    @24
    ad2antrr
    #
    wph
    cY
    @15
    wcel
    @1
    @31
    @25
    ad2antrr
    @60
    wph
    @1
    @31
    simplr
    @32
    @33
    cX
    cX
    @12
    co
    #
    wcel
    @56
    @57
    @32
    cC
    cU
    @33
    @12
    cV
    cX
    cX
    setcmon.c
    @51
    @18
    @53
    @53
    elsetchom
    mpbird
    @32
    @35
    @61
    wcel
    @58
    @59
    @32
    cC
    cU
    @35
    @12
    cV
    cX
    cX
    setcmon.c
    @51
    @18
    @53
    @53
    elsetchom
    mpbird
    moni
    mpbid
    fveq1d
    @32
    @28
    @34
    @5
    wceq
    @49
    cX
    @5
    @5
    vx
    vex
    fvconst2
    syl
    @32
    @28
    @36
    @7
    wceq
    @49
    cX
    @7
    @5
    vy
    vex
    fvconst2
    syl
    3eqtr3d
    expr
    ralrimivva
    vx
    vy
    cX
    cY
    cF
    dff13
    sylanbrc
    wph
    @2
    wa
    #
    @1
    @14
    cF
    vg
    cv
    #
    vz
    cv
    #
    cX
    cop
    cY
    @16
    co
    #
    co
    #
    cF
    vh
    cv
    #
    @65
    co
    #
    wceq
    #
    @63
    @67
    wceq
    #
    wi
    #
    vh
    @64
    cX
    @12
    co
    #
    wral
    vg
    @72
    wral
    #
    vz
    @15
    wral
    #
    @2
    wph
    @4
    @14
    cX
    cY
    cF
    f1f
    #
    wph
    @14
    @4
    @26
    biimpar
    sylan2
    @62
    @73
    vz
    @15
    @62
    @64
    @15
    wcel
    @64
    cU
    wcel
    #
    @73
    @62
    cU
    @15
    @64
    wph
    cU
    @15
    wceq
    @2
    @23
    adantr
    eleq2d
    @62
    @76
    @73
    @62
    @76
    wa
    @71
    vg
    vh
    @72
    @72
    @62
    @76
    @63
    @72
    wcel
    #
    @67
    @72
    wcel
    #
    wa
    #
    @71
    @62
    @76
    @79
    wa
    #
    wa
    #
    @69
    cF
    @63
    ccom
    #
    cF
    @67
    ccom
    #
    wceq
    #
    @70
    @81
    @66
    @82
    @68
    @83
    @81
    cC
    @16
    cU
    @63
    cF
    cV
    @64
    cX
    cY
    setcmon.c
    wph
    @20
    @2
    @80
    setcmon.u
    ad2antrr
    #
    @19
    @62
    @76
    @79
    simprl
    #
    wph
    @52
    @2
    @80
    setcmon.x
    ad2antrr
    #
    wph
    @54
    @2
    @80
    setcmon.y
    ad2antrr
    #
    @81
    @77
    @64
    cX
    @63
    wf
    #
    @62
    @76
    @77
    @78
    simprrl
    @81
    cC
    cU
    @63
    @12
    cV
    @64
    cX
    setcmon.c
    @85
    @18
    @86
    @87
    elsetchom
    mpbid
    #
    @2
    @4
    wph
    @80
    @75
    ad2antlr
    #
    setcco
    @81
    cC
    @16
    cU
    @67
    cF
    cV
    @64
    cX
    cY
    setcmon.c
    @85
    @19
    @86
    @87
    @88
    @81
    @78
    @64
    cX
    @67
    wf
    #
    @62
    @76
    @77
    @78
    simprrr
    @81
    cC
    cU
    @67
    @12
    cV
    @64
    cX
    setcmon.c
    @85
    @18
    @86
    @87
    elsetchom
    mpbid
    #
    @91
    setcco
    eqeq12d
    @81
    @84
    @70
    @81
    @2
    @89
    @92
    @84
    @70
    wb
    wph
    @2
    @80
    simplr
    @90
    @93
    @64
    cX
    cY
    cF
    @63
    @67
    cocan1
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
    @14
    @74
    wa
    wb
    @2
    wph
    vz
    @15
    cC
    @16
    vg
    vh
    cF
    @12
    cM
    cX
    cY
    @17
    @18
    @19
    setcmon.h
    @22
    @24
    @25
    ismon2
    adantr
    mpbir2and
    impbida
end
