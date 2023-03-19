include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cr.mm"
include "cdv.mm"
include "cc0.mm"
include "wceq.mm"
include "cioo.mm"
include "ltled.mm"
include "evthicc.mm"
include "reeanv.mm"
include "sylibr.mm"
include "wcel.mm"
include "r19.26.mm"
include "cpr.mm"
include "wn.mm"
include "ad2antrr.mm"
include "clt.mm"
include "ccncf.mm"
include "cdm.mm"
include "simpl.mm"
include "ralimi.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ad2antrl.mm"
include "simplrl.mm"
include "simprr.mm"
include "rollelem.mm"
include "expr.mm"
include "cneg.mm"
include "cmpt.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "renegcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "sseldi.mm"
include "negfcncf.mm"
include "cncffvrn.mm"
include "sylancr.mm"
include "mpbird.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "a1i.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "fss.mm"
include "sylancl.mm"
include "negcld.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cvv.mm"
include "reelprrecn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "dvf.mm"
include "feq2d.mm"
include "mpbii.mm"
include "3eqtr3rd.mm"
include "dvmptneg.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "dmmptg.mm"
include "negex.mm"
include "mprg.mm"
include "syl6eq.mm"
include "simpr.mm"
include "simplrr.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "lenegd.mm"
include "negeqd.mm"
include "fvmpt.mm"
include "adantl.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "syl5ib.mm"
include "ralimdva.mm"
include "imp.mm"
include "adantrr.mm"
include "fveq1d.mm"
include "sylan9eq.mm"
include "eqeq1d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "ffvelrni.mm"
include "negeq0d.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "wi.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "eqcomd.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "chvarv.mm"
include "anim12d.mm"
include "cxr.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "letri3d.mm"
include "breq2.mm"
include "breq1.mm"
include "bi2anan9.mm"
include "bibi2d.mm"
include "impancom.mm"
include "ralbidva.mm"
include "csn.mm"
include "cxp.mm"
include "wfn.mm"
include "ffn.mm"
include "fnconstg.mm"
include "eqfnfv.mm"
include "fvex.mm"
include "fvconst2.mm"
include "eqeq2d.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "fconstmpt.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "recnd.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptres2.mm"
include "sylan9eqr.mm"
include "eqidd.mm"
include "c0ex.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wne.mm"
include "ioon0.mm"
include "r19.2z.mm"
include "sylan.mm"
include "syldan.mm"
include "ex.mm"
include "sylbird.mm"
include "syld.mm"
include "ecased.mm"
include "syl5bir.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem rolle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let cU: class U
  assume rolle.a: |- ( ph -> A e. RR )
  assume rolle.b: |- ( ph -> B e. RR )
  assume rolle.lt: |- ( ph -> A < B )
  assume rolle.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume rolle.d: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume rolle.e: |- ( ph -> ( F ` A ) = ( F ` B ) )

  disjoint A x
  disjoint ph x
  disjoint B x
  disjoint F x
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A y
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph y
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U y
  assert |- ( ph -> E. x e. ( A (,) B ) ( ( RR _D F ) ` x ) = 0 )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    vu
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    #
    vv
    cv
    #
    cF
    cfv
    #
    @1
    cle
    wbr
    #
    vy
    @5
    wral
    #
    wa
    #
    vv
    @5
    wrex
    vu
    @5
    wrex
    #
    vx
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cc0
    wceq
    #
    vx
    cA
    cB
    cioo
    co
    #
    wrex
    #
    wph
    @6
    vu
    @5
    wrex
    @10
    vv
    @5
    wrex
    wa
    @12
    wph
    vu
    vy
    vv
    vy
    cA
    cB
    cF
    rolle.a
    rolle.b
    wph
    cA
    cB
    rolle.a
    rolle.b
    rolle.lt
    ltled
    #
    rolle.f
    evthicc
    @6
    @10
    vu
    vv
    @5
    @5
    reeanv
    sylibr
    wph
    @11
    @18
    vu
    vv
    @5
    @5
    @11
    @4
    @9
    wa
    #
    vy
    @5
    wral
    #
    wph
    @2
    @5
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    #
    wa
    #
    @18
    @4
    @9
    vy
    @5
    r19.26
    @25
    @21
    @18
    @25
    @21
    wa
    #
    @2
    cA
    cB
    cpr
    #
    wcel
    #
    @7
    @27
    wcel
    #
    @18
    @25
    @21
    @28
    wn
    #
    @18
    @25
    @21
    @30
    wa
    #
    wa
    vx
    vt
    cA
    cB
    @2
    cF
    wph
    cA
    cr
    wcel
    #
    @24
    @31
    rolle.a
    ad2antrr
    wph
    cB
    cr
    wcel
    #
    @24
    @31
    rolle.b
    ad2antrr
    wph
    cA
    cB
    clt
    wbr
    #
    @24
    @31
    rolle.lt
    ad2antrr
    wph
    cF
    @5
    cr
    ccncf
    co
    #
    wcel
    #
    @24
    @31
    rolle.f
    ad2antrr
    wph
    @14
    cdm
    #
    @17
    wceq
    @24
    @31
    rolle.d
    ad2antrr
    @21
    vt
    cv
    #
    cF
    cfv
    #
    @3
    cle
    wbr
    #
    vt
    @5
    wral
    #
    @25
    @30
    @21
    @6
    @41
    @20
    @4
    vy
    @5
    @4
    @9
    simpl
    ralimi
    @4
    @40
    vy
    vt
    @5
    vy
    vt
    weq
    #
    @1
    @39
    @3
    cle
    @0
    @38
    cF
    fveq2
    breq1d
    cbvralv
    sylib
    ad2antrl
    wph
    @22
    @23
    @31
    simplrl
    @25
    @21
    @30
    simprr
    rollelem
    expr
    @25
    @21
    @29
    wn
    #
    @18
    @25
    @21
    @43
    wa
    #
    wa
    #
    @13
    cr
    vu
    @5
    @3
    cneg
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    cc0
    wceq
    #
    vx
    @17
    wrex
    #
    @18
    @45
    vx
    vt
    cA
    cB
    @7
    @47
    wph
    @32
    @24
    @44
    rolle.a
    ad2antrr
    wph
    @33
    @24
    @44
    rolle.b
    ad2antrr
    wph
    @34
    @24
    @44
    rolle.lt
    ad2antrr
    wph
    @47
    @35
    wcel
    #
    @24
    @44
    wph
    @52
    @5
    cr
    @47
    wf
    #
    wph
    vu
    @5
    @46
    cr
    @47
    wph
    @22
    wa
    #
    @3
    wph
    @5
    cr
    @2
    cF
    wph
    @36
    @5
    cr
    cF
    wf
    #
    rolle.f
    @5
    cr
    cF
    cncff
    syl
    #
    ffvelrnda
    renegcld
    @47
    eqid
    #
    fmptd
    wph
    cr
    cc
    wss
    #
    @47
    @5
    cc
    ccncf
    co
    #
    wcel
    #
    @52
    @53
    wb
    ax-resscn
    wph
    cF
    @59
    wcel
    @60
    wph
    @35
    @59
    cF
    @58
    cc
    cc
    wss
    @35
    @59
    wss
    ax-resscn
    cc
    ssid
    @5
    cr
    cc
    cncfss
    mp2an
    rolle.f
    sseldi
    vu
    @5
    cF
    @47
    @57
    negfcncf
    syl
    @5
    cc
    cr
    @47
    cncffvrn
    sylancr
    mpbird
    ad2antrr
    wph
    @48
    cdm
    #
    @17
    wceq
    @24
    @44
    wph
    @61
    vu
    @17
    @2
    @14
    cfv
    #
    cneg
    #
    cmpt
    #
    cdm
    #
    @17
    wph
    @48
    @64
    wph
    @48
    cr
    vu
    @17
    @46
    cmpt
    cdv
    co
    @64
    wph
    vu
    @46
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    @5
    @17
    @58
    wph
    ax-resscn
    a1i
    #
    wph
    @32
    @33
    @5
    cr
    wss
    rolle.a
    rolle.b
    cA
    cB
    iccssre
    syl2anc
    #
    @54
    @3
    wph
    @5
    cc
    @2
    cF
    wph
    @55
    @58
    @5
    cc
    cF
    wf
    @56
    ax-resscn
    @5
    cr
    cc
    cF
    fss
    sylancl
    ffvelrnda
    #
    negcld
    @67
    @67
    eqid
    #
    tgioo2
    #
    @71
    wph
    @32
    @33
    @5
    @66
    cnt
    cfv
    cfv
    @17
    wceq
    rolle.a
    rolle.b
    cA
    cB
    iccntr
    syl2anc
    #
    dvmptntr
    wph
    vu
    @3
    @62
    cr
    cvv
    @17
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @2
    @17
    wcel
    #
    wph
    @22
    @3
    cc
    wcel
    @17
    @5
    @2
    cA
    cB
    ioossicc
    sseli
    @70
    sylan2
    wph
    @75
    wa
    @2
    @14
    fvexd
    wph
    @14
    cr
    vu
    @5
    @3
    cmpt
    #
    cdv
    co
    vu
    @17
    @62
    cmpt
    cr
    vu
    @17
    @3
    cmpt
    cdv
    co
    wph
    cF
    @76
    cr
    cdv
    wph
    vu
    @5
    cr
    cF
    @56
    feqmptd
    oveq2d
    wph
    vu
    @17
    cc
    @14
    wph
    @37
    cc
    @14
    wf
    @17
    cc
    @14
    wf
    cF
    dvf
    #
    wph
    @37
    @17
    cc
    @14
    rolle.d
    feq2d
    mpbii
    feqmptd
    wph
    vu
    @3
    cr
    @66
    @67
    @5
    @17
    @68
    @69
    @70
    @72
    @71
    @73
    dvmptntr
    3eqtr3rd
    dvmptneg
    eqtrd
    #
    dmeqd
    @63
    cvv
    wcel
    #
    @65
    @17
    wceq
    vu
    @17
    vu
    @17
    @63
    cvv
    dmmptg
    @79
    @75
    @62
    negex
    a1i
    mprg
    syl6eq
    ad2antrr
    @25
    @21
    @38
    @47
    cfv
    #
    @7
    @47
    cfv
    #
    cle
    wbr
    #
    vt
    @5
    wral
    #
    @43
    @26
    @0
    @47
    cfv
    #
    @81
    cle
    wbr
    #
    vy
    @5
    wral
    #
    @83
    @25
    @21
    @86
    @25
    @20
    @85
    vy
    @5
    @20
    @9
    @25
    @0
    @5
    wcel
    #
    wa
    #
    @85
    @4
    @9
    simpr
    @88
    @9
    @1
    cneg
    #
    @8
    cneg
    #
    cle
    wbr
    @85
    @88
    @8
    @1
    @88
    @5
    cr
    @7
    cF
    wph
    @55
    @24
    @87
    @56
    ad2antrr
    wph
    @22
    @23
    @87
    simplrr
    #
    ffvelrnd
    @25
    @5
    cr
    @0
    cF
    wph
    @55
    @24
    @56
    adantr
    ffvelrnda
    #
    lenegd
    @88
    @84
    @89
    @81
    @90
    cle
    @87
    @84
    @89
    wceq
    @25
    vu
    @0
    @46
    @89
    @5
    @47
    vu
    vy
    weq
    @3
    @1
    @2
    @0
    cF
    fveq2
    negeqd
    @57
    @1
    negex
    fvmpt
    adantl
    @88
    @23
    @81
    @90
    wceq
    @91
    vu
    @7
    @46
    @90
    @5
    @47
    vu
    vv
    weq
    #
    @3
    @8
    @2
    @7
    cF
    fveq2
    #
    negeqd
    @57
    @8
    negex
    fvmpt
    syl
    breq12d
    bitr4d
    syl5ib
    ralimdva
    imp
    @85
    @82
    vy
    vt
    @5
    @42
    @84
    @80
    @81
    cle
    @0
    @38
    @47
    fveq2
    breq1d
    cbvralv
    sylib
    adantrr
    wph
    @22
    @23
    @44
    simplrr
    @25
    @21
    @43
    simprr
    rollelem
    wph
    @51
    @18
    wb
    @24
    @44
    wph
    @50
    @16
    vx
    @17
    wph
    @13
    @17
    wcel
    #
    wa
    #
    @50
    @15
    cneg
    #
    cc0
    wceq
    @16
    @96
    @49
    @97
    cc0
    wph
    @95
    @49
    @13
    @64
    cfv
    @97
    wph
    @13
    @48
    @64
    @78
    fveq1d
    vu
    @13
    @63
    @97
    @17
    @64
    vu
    vx
    weq
    #
    @62
    @15
    @2
    @13
    @14
    fveq2
    negeqd
    @64
    eqid
    @15
    negex
    fvmpt
    sylan9eq
    eqeq1d
    @96
    @15
    @96
    @13
    @37
    wcel
    #
    @15
    cc
    wcel
    wph
    @99
    @95
    wph
    @37
    @17
    @13
    rolle.d
    eleq2d
    biimpar
    @37
    cc
    @13
    @14
    @77
    ffvelrni
    syl
    negeq0d
    bitr4d
    rexbidva
    ad2antrr
    mpbid
    expr
    @26
    @28
    @29
    wa
    #
    @3
    cA
    cF
    cfv
    #
    wceq
    #
    @8
    @101
    wceq
    #
    wa
    #
    @18
    wph
    @100
    @104
    wi
    @24
    @21
    wph
    @28
    @102
    @29
    @103
    @28
    @2
    cA
    wceq
    #
    @2
    cB
    wceq
    #
    wo
    wph
    @102
    @2
    cA
    cB
    vu
    vex
    elpr
    wph
    @105
    @102
    @106
    @105
    @102
    wi
    wph
    @2
    cA
    cF
    fveq2
    a1i
    wph
    @102
    @106
    cB
    cF
    cfv
    #
    @101
    wceq
    wph
    @101
    @107
    rolle.e
    eqcomd
    @106
    @3
    @107
    @101
    @2
    cB
    cF
    fveq2
    eqeq1d
    syl5ibrcom
    jaod
    syl5bi
    #
    wph
    @28
    @102
    wi
    #
    wi
    wph
    @29
    @103
    wi
    #
    wi
    vu
    vv
    @93
    @109
    @110
    wph
    @93
    @28
    @29
    @102
    @103
    @2
    @7
    @27
    eleq1
    @93
    @3
    @8
    @101
    @94
    eqeq1d
    imbi12d
    imbi2d
    @108
    chvarv
    anim12d
    ad2antrr
    @25
    @104
    @21
    @18
    @25
    @104
    wa
    #
    @21
    @1
    @101
    wceq
    #
    vy
    @5
    wral
    #
    @18
    @111
    @112
    @20
    vy
    @5
    @111
    @87
    @112
    @20
    wb
    #
    @25
    @87
    @104
    @114
    @88
    @114
    @104
    @112
    @1
    @101
    cle
    wbr
    #
    @101
    @1
    cle
    wbr
    #
    wa
    #
    wb
    @88
    @1
    @101
    @92
    wph
    @101
    cr
    wcel
    #
    @24
    @87
    wph
    @5
    cr
    cA
    cF
    @56
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    cA
    @5
    wcel
    wph
    cA
    rolle.a
    rexrd
    #
    wph
    cB
    rolle.b
    rexrd
    #
    @19
    cA
    cB
    lbicc2
    syl3anc
    ffvelrnd
    #
    ad2antrr
    letri3d
    @104
    @20
    @117
    @112
    @102
    @4
    @115
    @103
    @9
    @116
    @3
    @101
    @1
    cle
    breq2
    @8
    @101
    @1
    cle
    breq1
    bi2anan9
    bibi2d
    syl5ibrcom
    impancom
    imp
    ralbidva
    wph
    @113
    @18
    wi
    @24
    @104
    wph
    @113
    cF
    @5
    @101
    csn
    cxp
    #
    wceq
    #
    @18
    wph
    @125
    @1
    @0
    @124
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    #
    @113
    wph
    cF
    @5
    wfn
    #
    @124
    @5
    wfn
    #
    @125
    @128
    wb
    wph
    @55
    @129
    @56
    @5
    cr
    cF
    ffn
    syl
    wph
    @118
    @130
    @123
    @5
    @101
    cr
    fnconstg
    syl
    vy
    @5
    cF
    @124
    eqfnfv
    syl2anc
    @127
    @112
    vy
    @5
    @87
    @126
    @101
    @1
    @5
    @101
    @0
    cA
    cF
    fvex
    fvconst2
    eqeq2d
    ralbiia
    syl6bb
    wph
    @125
    @18
    wph
    @125
    @16
    vx
    @17
    wral
    #
    @18
    wph
    @125
    wa
    #
    @16
    vx
    @17
    @132
    @95
    @15
    @13
    vu
    @17
    cc0
    cmpt
    #
    cfv
    cc0
    @132
    @13
    @14
    @133
    @125
    wph
    @14
    cr
    vu
    @5
    @101
    cmpt
    #
    cdv
    co
    @133
    @125
    cF
    @134
    cr
    cdv
    @125
    cF
    @134
    wceq
    @124
    @134
    cF
    vu
    @5
    @101
    fconstmpt
    eqeq2i
    biimpi
    oveq2d
    wph
    vu
    @101
    cc0
    cr
    @66
    @67
    cc
    cr
    @17
    @5
    @74
    wph
    @101
    cc
    wcel
    @2
    cr
    wcel
    #
    wph
    @101
    @123
    recnd
    #
    adantr
    wph
    @135
    wa
    0cnd
    wph
    vu
    @101
    cr
    @74
    @136
    dvmptc
    @69
    @72
    @71
    @73
    dvmptres2
    sylan9eqr
    fveq1d
    vu
    @13
    cc0
    cc0
    @17
    @133
    @98
    cc0
    eqidd
    @133
    eqid
    c0ex
    fvmpt
    sylan9eq
    ralrimiva
    wph
    @17
    c0
    wne
    #
    @131
    @18
    wph
    @137
    @34
    rolle.lt
    wph
    @119
    @120
    @137
    @34
    wb
    @121
    @122
    cA
    cB
    ioon0
    syl2anc
    mpbird
    @16
    vx
    @17
    r19.2z
    sylan
    syldan
    ex
    sylbird
    ad2antrr
    sylbird
    impancom
    syld
    ecased
    ex
    syl5bir
    rexlimdvva
    mpd
end
