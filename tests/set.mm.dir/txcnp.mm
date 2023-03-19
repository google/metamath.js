include "cop.mm"
include "cmpt.mm"
include "ctx.mm"
include "co.mm"
include "ccnp.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "ctopon.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "wb.mm"
include "wceq.mm"
include "cvv.mm"
include "simpr.mm"
include "opex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "opeq12d.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfop.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "sylc.mm"
include "eleq1d.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simprl.mm"
include "cnpimaex.mm"
include "simplrr.mm"
include "simprr.mm"
include "jca.mm"
include "ex.mm"
include "opelxp.mm"
include "reeanv.mm"
include "3imtr4g.mm"
include "sylbid.mm"
include "cin.mm"
include "an4.mm"
include "elin.mm"
include "biimpri.mm"
include "a1i.mm"
include "simpl.mm"
include "toponss.mm"
include "syl2an.mm"
include "ssinss1.mm"
include "adantl.mm"
include "sselda.mm"
include "inss1.mm"
include "sseldi.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "syl.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "sseldd.mm"
include "funfvima.mm"
include "mpd.mm"
include "inss2.mm"
include "eqeltrd.mm"
include "funimass4.mm"
include "mpbird.mm"
include "syldan.mm"
include "adantlr.mm"
include "xpss12.mm"
include "sstr2.mm"
include "syl2im.mm"
include "anim12d.mm"
include "syl5bi.mm"
include "ctop.mm"
include "topontop.mm"
include "inopn.mm"
include "3expb.mm"
include "sylan.mm"
include "jctild.mm"
include "expimpd.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl6.mm"
include "expd.mm"
include "rexlimdvv.mm"
include "syld.mm"
include "ralrimivva.mm"
include "vex.mm"
include "xpex.mm"
include "rgen2w.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralrnmpt2.mm"
include "ax-mp.mm"
include "ctg.mm"
include "txval.mm"
include "txtopon.mm"
include "tgcnp.mm"
include "mpbir2and.mm"

theorem txcnp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume txcnp.4: |- ( ph -> J e. ( TopOn ` X ) )
  assume txcnp.5: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txcnp.6: |- ( ph -> L e. ( TopOn ` Z ) )
  assume txcnp.7: |- ( ph -> D e. X )
  assume txcnp.8: |- ( ph -> ( x e. X |-> A ) e. ( ( J CnP K ) ` D ) )
  assume txcnp.9: |- ( ph -> ( x e. X |-> B ) e. ( ( J CnP L ) ` D ) )

  disjoint ph x
  disjoint Y x
  disjoint Z x
  disjoint D x
  disjoint X x
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r x
  disjoint ph r
  disjoint s x
  disjoint ph s
  disjoint t x
  disjoint ph t
  disjoint v x
  disjoint ph v
  disjoint w x
  disjoint ph w
  disjoint x z
  disjoint ph z
  disjoint x y
  disjoint Y y
  disjoint Y z
  disjoint Z y
  disjoint Z z
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint D r
  disjoint D s
  disjoint D v
  disjoint D w
  disjoint D y
  disjoint D z
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint J r
  disjoint J s
  disjoint J v
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint K r
  disjoint K s
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint L r
  disjoint L s
  disjoint L v
  disjoint L w
  disjoint L y
  disjoint L z
  assert |- ( ph -> ( x e. X |-> <. A , B >. ) e. ( ( J CnP ( K tX L ) ) ` D ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cop
    #
    cmpt
    #
    cD
    cJ
    cK
    cL
    ctx
    co
    #
    ccnp
    co
    cfv
    wcel
    cX
    cY
    cZ
    cxp
    #
    @1
    wf
    #
    cD
    @1
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cD
    vz
    cv
    #
    wcel
    #
    @1
    @8
    cima
    #
    @6
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    wi
    #
    vy
    vv
    vw
    cK
    cL
    vv
    cv
    #
    vw
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    wral
    #
    wph
    vx
    cX
    @0
    @3
    @1
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    cA
    cY
    wcel
    #
    cB
    cZ
    wcel
    #
    @0
    @3
    wcel
    wph
    @24
    vx
    cX
    wph
    cX
    cY
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @24
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @26
    cD
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    @27
    txcnp.4
    txcnp.5
    txcnp.8
    cD
    @26
    cJ
    cK
    cX
    cY
    cnpf2
    syl3anc
    #
    vx
    cX
    cY
    cA
    @26
    @26
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    #
    wph
    @25
    vx
    cX
    wph
    cX
    cZ
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @25
    vx
    cX
    wral
    wph
    @28
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @34
    cD
    cJ
    cL
    ccnp
    co
    cfv
    wcel
    #
    @35
    txcnp.4
    txcnp.6
    txcnp.9
    cD
    @34
    cJ
    cL
    cX
    cZ
    cnpf2
    syl3anc
    #
    vx
    cX
    cZ
    cB
    @34
    @34
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    #
    cA
    cB
    cY
    cZ
    opelxpi
    syl2anc
    @1
    eqid
    #
    fmptd
    #
    wph
    @5
    @17
    wcel
    #
    @9
    @10
    @17
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    wi
    #
    vw
    cL
    wral
    vv
    cK
    wral
    #
    @20
    wph
    @47
    vv
    vw
    cK
    cL
    wph
    @15
    cK
    wcel
    #
    @16
    cL
    wcel
    #
    wa
    #
    wa
    #
    @43
    cD
    vr
    cv
    #
    wcel
    #
    @26
    @53
    cima
    #
    @15
    wss
    #
    wa
    #
    cD
    vs
    cv
    #
    wcel
    #
    @34
    @58
    cima
    #
    @16
    wss
    #
    wa
    #
    wa
    #
    vs
    cJ
    wrex
    vr
    cJ
    wrex
    #
    @46
    @52
    @43
    cD
    @26
    cfv
    #
    cD
    @34
    cfv
    #
    cop
    #
    @17
    wcel
    #
    @64
    wph
    @43
    @68
    wb
    @51
    wph
    @5
    @67
    @17
    wph
    cD
    cX
    wcel
    @21
    @1
    cfv
    #
    @21
    @26
    cfv
    #
    @21
    @34
    cfv
    #
    cop
    #
    wceq
    #
    vx
    cX
    wral
    #
    @5
    @67
    wceq
    #
    txcnp.7
    wph
    @73
    vx
    cX
    @23
    @69
    @0
    @72
    @23
    @22
    @0
    cvv
    wcel
    @69
    @0
    wceq
    wph
    @22
    simpr
    #
    cA
    cB
    opex
    vx
    cX
    @0
    cvv
    @1
    @41
    fvmpt2
    sylancl
    @23
    @70
    cA
    @71
    cB
    @23
    @22
    @24
    @70
    cA
    wceq
    @76
    @33
    vx
    cX
    cA
    cY
    @26
    @32
    fvmpt2
    syl2anc
    @23
    @22
    @25
    @71
    cB
    wceq
    @76
    @40
    vx
    cX
    cB
    cZ
    @34
    @39
    fvmpt2
    syl2anc
    opeq12d
    eqtr4d
    ralrimiva
    #
    @73
    @75
    vx
    cD
    cX
    vx
    @5
    @67
    vx
    cX
    @0
    cD
    nffvmpt1
    vx
    @65
    @66
    vx
    cX
    cA
    cD
    nffvmpt1
    vx
    cX
    cB
    cD
    nffvmpt1
    nfop
    nfeq
    @21
    cD
    wceq
    #
    @69
    @5
    @72
    @67
    @21
    cD
    @1
    fveq2
    @78
    @70
    @65
    @71
    @66
    @21
    cD
    @26
    fveq2
    @21
    cD
    @34
    fveq2
    opeq12d
    eqeq12d
    rspc
    sylc
    eleq1d
    adantr
    @52
    @65
    @15
    wcel
    #
    @66
    @16
    wcel
    #
    wa
    #
    @57
    vr
    cJ
    wrex
    #
    @62
    vs
    cJ
    wrex
    #
    wa
    #
    @68
    @64
    @52
    @81
    @84
    @52
    @81
    wa
    #
    @82
    @83
    @85
    @30
    @49
    @79
    @82
    wph
    @30
    @51
    @81
    txcnp.8
    ad2antrr
    wph
    @49
    @50
    @81
    simplrl
    @52
    @79
    @80
    simprl
    vr
    @15
    cD
    @26
    cJ
    cK
    cnpimaex
    syl3anc
    @85
    @37
    @50
    @80
    @83
    wph
    @37
    @51
    @81
    txcnp.9
    ad2antrr
    wph
    @49
    @50
    @81
    simplrr
    @52
    @79
    @80
    simprr
    vs
    @16
    cD
    @34
    cJ
    cL
    cnpimaex
    syl3anc
    jca
    ex
    @65
    @66
    @15
    @16
    opelxp
    @57
    @62
    vr
    vs
    cJ
    cJ
    reeanv
    3imtr4g
    sylbid
    @52
    @63
    @46
    vr
    vs
    cJ
    cJ
    @52
    @53
    cJ
    wcel
    #
    @58
    cJ
    wcel
    #
    wa
    #
    @63
    @46
    @52
    @88
    @63
    wa
    @53
    @58
    cin
    #
    cJ
    wcel
    #
    cD
    @89
    wcel
    #
    @1
    @89
    cima
    #
    @17
    wss
    #
    wa
    #
    wa
    #
    @46
    @52
    @88
    @63
    @95
    @52
    @88
    wa
    #
    @63
    @94
    @90
    @63
    @54
    @59
    wa
    #
    @56
    @61
    wa
    #
    wa
    @96
    @94
    @54
    @56
    @59
    @61
    an4
    @96
    @97
    @91
    @98
    @93
    @97
    @91
    wi
    @96
    @91
    @97
    cD
    @53
    @58
    elin
    biimpri
    a1i
    @96
    @92
    @55
    @60
    cxp
    #
    wss
    #
    @98
    @99
    @17
    wss
    @93
    wph
    @88
    @100
    @51
    wph
    @88
    @53
    cX
    wss
    #
    @100
    wph
    @28
    @86
    @101
    @88
    txcnp.4
    @86
    @87
    simpl
    @53
    cJ
    cX
    toponss
    syl2an
    wph
    @101
    wa
    #
    @100
    vt
    cv
    #
    @1
    cfv
    #
    @99
    wcel
    #
    vt
    @89
    wral
    #
    @102
    @105
    vt
    @89
    @102
    @103
    @89
    wcel
    #
    wa
    #
    @104
    @103
    @26
    cfv
    #
    @103
    @34
    cfv
    #
    cop
    #
    @99
    @108
    @103
    cX
    wcel
    @74
    @104
    @111
    wceq
    #
    @102
    @89
    cX
    @103
    @101
    @89
    cX
    wss
    #
    wph
    @53
    @58
    cX
    ssinss1
    adantl
    #
    sselda
    wph
    @74
    @101
    @107
    @77
    ad2antrr
    @73
    @112
    vx
    @103
    cX
    vx
    @104
    @111
    vx
    cX
    @0
    @103
    nffvmpt1
    vx
    @109
    @110
    vx
    cX
    cA
    @103
    nffvmpt1
    vx
    cX
    cB
    @103
    nffvmpt1
    nfop
    nfeq
    @21
    @103
    wceq
    #
    @69
    @104
    @72
    @111
    @21
    @103
    @1
    fveq2
    @115
    @70
    @109
    @71
    @110
    @21
    @103
    @26
    fveq2
    @21
    @103
    @34
    fveq2
    opeq12d
    eqeq12d
    rspc
    sylc
    @108
    @109
    @55
    wcel
    #
    @110
    @60
    wcel
    #
    @111
    @99
    wcel
    @108
    @103
    @53
    wcel
    #
    @116
    @108
    @89
    @53
    @103
    @53
    @58
    inss1
    @102
    @107
    simpr
    #
    sseldi
    @108
    @26
    wfun
    #
    @103
    @26
    cdm
    #
    wcel
    @118
    @116
    wi
    @108
    @27
    @120
    wph
    @27
    @101
    @107
    @31
    ad2antrr
    #
    cX
    cY
    @26
    ffun
    syl
    @108
    @89
    @121
    @103
    @108
    @89
    cX
    @121
    @102
    @113
    @107
    @114
    adantr
    #
    @108
    @27
    @121
    cX
    wceq
    @122
    cX
    cY
    @26
    fdm
    syl
    sseqtr4d
    @119
    sseldd
    @53
    @103
    @26
    funfvima
    syl2anc
    mpd
    @108
    @103
    @58
    wcel
    #
    @117
    @108
    @89
    @58
    @103
    @53
    @58
    inss2
    @119
    sseldi
    @108
    @34
    wfun
    #
    @103
    @34
    cdm
    #
    wcel
    @124
    @117
    wi
    @108
    @35
    @125
    wph
    @35
    @101
    @107
    @38
    ad2antrr
    #
    cX
    cZ
    @34
    ffun
    syl
    @108
    @89
    @126
    @103
    @108
    @89
    cX
    @126
    @123
    @108
    @35
    @126
    cX
    wceq
    @127
    cX
    cZ
    @34
    fdm
    syl
    sseqtr4d
    @119
    sseldd
    @58
    @103
    @34
    funfvima
    syl2anc
    mpd
    @109
    @110
    @55
    @60
    opelxpi
    syl2anc
    eqeltrd
    ralrimiva
    @102
    @1
    wfun
    #
    @89
    @1
    cdm
    #
    wss
    @100
    @106
    wb
    wph
    @128
    @101
    wph
    @4
    @128
    @42
    cX
    @3
    @1
    ffun
    syl
    adantr
    @102
    @89
    cX
    @129
    @114
    wph
    @129
    cX
    wceq
    #
    @101
    wph
    @4
    @130
    @42
    cX
    @3
    @1
    fdm
    syl
    adantr
    sseqtr4d
    vt
    @89
    @99
    @1
    funimass4
    syl2anc
    mpbird
    syldan
    adantlr
    @55
    @15
    @60
    @16
    xpss12
    @92
    @99
    @17
    sstr2
    syl2im
    anim12d
    syl5bi
    wph
    @88
    @90
    @51
    wph
    cJ
    ctop
    wcel
    #
    @88
    @90
    wph
    @28
    @131
    txcnp.4
    cX
    cJ
    topontop
    syl
    @131
    @86
    @87
    @90
    @53
    @58
    cJ
    inopn
    3expb
    sylan
    adantlr
    jctild
    expimpd
    @45
    @94
    vz
    @89
    cJ
    @8
    @89
    wceq
    #
    @9
    @91
    @44
    @93
    @8
    @89
    cD
    eleq2
    @132
    @10
    @92
    @17
    @8
    @89
    @1
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl6
    expd
    rexlimdvv
    syld
    ralrimivva
    @17
    cvv
    wcel
    #
    vw
    cL
    wral
    vv
    cK
    wral
    @20
    @48
    wb
    @133
    vv
    vw
    cK
    cL
    @15
    @16
    vv
    vex
    vw
    vex
    xpex
    rgen2w
    @14
    @47
    vv
    vw
    vy
    cK
    cL
    @17
    @18
    cvv
    @18
    eqid
    @6
    @17
    wceq
    #
    @7
    @43
    @13
    @46
    @6
    @17
    @5
    eleq2
    @134
    @12
    @45
    vz
    cJ
    @134
    @11
    @44
    @9
    @6
    @17
    @10
    sseq2
    anbi2d
    rexbidv
    imbi12d
    ralrnmpt2
    ax-mp
    sylibr
    wph
    vz
    vy
    @19
    cD
    @1
    cJ
    @2
    cX
    @3
    txcnp.4
    wph
    cK
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    @2
    @19
    ctg
    cfv
    wceq
    wph
    @29
    @135
    txcnp.5
    cY
    cK
    topontop
    syl
    wph
    @36
    @136
    txcnp.6
    cZ
    cL
    topontop
    syl
    vv
    vw
    @19
    cK
    cL
    ctop
    ctop
    @19
    eqid
    txval
    syl2anc
    wph
    @29
    @36
    @2
    @3
    ctopon
    cfv
    wcel
    txcnp.5
    txcnp.6
    cK
    cL
    cY
    cZ
    txtopon
    syl2anc
    txcnp.7
    tgcnp
    mpbir2and
end
