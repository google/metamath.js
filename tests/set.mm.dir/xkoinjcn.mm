include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cxko.mm"
include "ccn.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "crest.mm"
include "ccmp.mm"
include "cuni.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "cop.mm"
include "cmpt.mm"
include "simplr.mm"
include "cnmptid.mm"
include "simpll.mm"
include "simpr.mm"
include "cnmptc.mm"
include "cnmpt1t.mm"
include "fmptd.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "xkobval.mm"
include "abeq2i.mm"
include "csn.mm"
include "cxp.mm"
include "wb.mm"
include "sylan.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "elrab3.mm"
include "syl.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "simplrl.mm"
include "elpwid.mm"
include "simprd.mm"
include "toponuni.mm"
include "sseqtr4d.mm"
include "adantr.mm"
include "cvv.mm"
include "dmmptg.mm"
include "opex.mm"
include "a1i.mm"
include "mprg.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "sylancr.mm"
include "wel.mm"
include "sselda.mm"
include "opeq1.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "vex.mm"
include "weq.mm"
include "opeq2.mm"
include "ralsn.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "eleq1.mm"
include "ralxp.mm"
include "bitri.mm"
include "3bitrd.mm"
include "rabbidva.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "elrab.mm"
include "cin.mm"
include "ctop.mm"
include "ad2antrr.mm"
include "topontop.mm"
include "adantl.mm"
include "txtop.mm"
include "syl2anc.mm"
include "ad3antrrr.mm"
include "toponmax.mm"
include "xpexg.mm"
include "simprr.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "txrest.mm"
include "syl22anc.mm"
include "oveq2d.mm"
include "restid.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "resttopon.mm"
include "xpeq1d.mm"
include "simprl.mm"
include "snssd.mm"
include "xpss2.mm"
include "ssind.mm"
include "eqsstr3d.mm"
include "txtube.mm"
include "toponss.mm"
include "ssrab.mm"
include "baib.mm"
include "biantrud.mm"
include "ciun.mm"
include "iunid.mm"
include "xpeq2i.mm"
include "xpiundi.mm"
include "eqtr3i.mm"
include "sseq1i.mm"
include "iunss.mm"
include "ssin.mm"
include "3bitr3g.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "eltop2.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "imaeq2.mm"
include "mptpreima.mm"
include "syl6eq.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "simpl.mm"
include "ovex.mm"
include "pwex.mm"
include "xkotf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "cfi.mm"
include "ctg.mm"
include "xkoval.mm"
include "xkotopon.mm"
include "subbascn.mm"
include "mpbir2and.mm"

theorem xkoinjcn
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cF: class F
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vt: setvar t
  assume xkoinjcn.3: |- F = ( x e. X |-> ( y e. Y |-> <. y , x >. ) )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint Y x
  disjoint Y y
  disjoint X x
  disjoint X y
  disjoint f k
  disjoint f r
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint R f
  disjoint k r
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint R k
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint R w
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S f
  disjoint S k
  disjoint S r
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint Y f
  disjoint Y k
  disjoint Y r
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint k t
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F k
  disjoint F v
  disjoint F z
  disjoint X k
  disjoint X r
  disjoint X v
  disjoint X w
  disjoint X z
  assert |- ( ( R e. ( TopOn ` X ) /\ S e. ( TopOn ` Y ) ) -> F e. ( R Cn ( ( S tX R ) ^ko S ) ) )

  proof
    cR
    cX
    ctopon
    cfv
    #
    wcel
    #
    cS
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cR
    cS
    cR
    ctx
    co
    #
    cS
    cxko
    co
    #
    ccn
    co
    wcel
    cX
    cS
    @4
    ccn
    co
    #
    cF
    wf
    cF
    ccnv
    #
    vz
    cv
    #
    cima
    #
    cR
    wcel
    #
    vz
    vk
    vv
    cS
    vw
    cv
    #
    crest
    co
    ccmp
    wcel
    vw
    cS
    cuni
    #
    cpw
    #
    crab
    #
    @4
    vf
    cv
    #
    vk
    cv
    #
    cima
    #
    vv
    cv
    #
    wss
    #
    vf
    @6
    crab
    #
    cmpt2
    #
    crn
    #
    wral
    @3
    vx
    cX
    vy
    cY
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    cmpt
    #
    @6
    cF
    @3
    @24
    cX
    wcel
    #
    wa
    #
    vy
    @23
    @24
    cS
    cS
    cR
    cY
    @1
    @2
    @27
    simplr
    #
    @28
    vy
    cS
    cY
    @29
    cnmptid
    @28
    vy
    @24
    cS
    cR
    cY
    cX
    @29
    @1
    @2
    @27
    simpll
    @3
    @27
    simpr
    cnmptc
    cnmpt1t
    #
    xkoinjcn.3
    fmptd
    @3
    @10
    vz
    @22
    @8
    @22
    wcel
    cS
    @16
    crest
    co
    #
    ccmp
    wcel
    #
    @8
    @20
    wceq
    #
    wa
    #
    vv
    @4
    wrex
    vk
    @13
    wrex
    #
    @3
    @10
    @35
    vz
    @22
    vw
    vv
    cS
    @4
    @21
    vf
    vk
    @14
    @12
    vz
    @12
    eqid
    #
    @14
    eqid
    #
    @21
    eqid
    #
    xkobval
    abeq2i
    @3
    @34
    @10
    vk
    vv
    @13
    @4
    @3
    @16
    @13
    wcel
    #
    @18
    @4
    wcel
    #
    wa
    #
    wa
    #
    @32
    @33
    @10
    @42
    @32
    wa
    #
    @10
    @33
    @26
    @20
    wcel
    #
    vx
    cX
    crab
    #
    cR
    wcel
    @43
    @45
    @16
    @24
    csn
    #
    cxp
    #
    @18
    wss
    #
    vx
    cX
    crab
    #
    cR
    @43
    @44
    @48
    vx
    cX
    @43
    @27
    wa
    #
    @44
    @26
    @16
    cima
    #
    @18
    wss
    #
    @8
    @26
    cfv
    #
    @18
    wcel
    #
    vz
    @16
    wral
    #
    @48
    @50
    @26
    @6
    wcel
    #
    @44
    @52
    wb
    @43
    @3
    @27
    @56
    @3
    @41
    @32
    simpll
    #
    @30
    sylan
    @19
    @52
    vf
    @26
    @6
    @15
    @26
    wceq
    @17
    @51
    @18
    @15
    @26
    @16
    imaeq1
    sseq1d
    elrab3
    syl
    @50
    @26
    wfun
    @16
    @26
    cdm
    #
    wss
    @52
    @55
    wb
    vy
    cY
    @25
    funmpt
    @50
    @16
    cY
    @58
    @43
    @16
    cY
    wss
    #
    @27
    @43
    @16
    @12
    cY
    @43
    @16
    @12
    @3
    @39
    @40
    @32
    simplrl
    elpwid
    @43
    @2
    cY
    @12
    wceq
    @43
    @1
    @2
    @57
    simprd
    #
    cY
    cS
    toponuni
    syl
    sseqtr4d
    #
    adantr
    #
    @25
    cvv
    wcel
    #
    @58
    cY
    wceq
    vy
    cY
    vy
    cY
    @25
    cvv
    dmmptg
    @63
    @23
    cY
    wcel
    @23
    @24
    opex
    a1i
    mprg
    syl6sseqr
    vz
    @16
    @18
    @26
    funimass4
    sylancr
    @50
    @55
    @8
    @11
    cop
    #
    @18
    wcel
    #
    vw
    @46
    wral
    #
    vz
    @16
    wral
    #
    @48
    @50
    @54
    @66
    vz
    @16
    @50
    vz
    vk
    wel
    wa
    #
    @54
    @8
    @24
    cop
    #
    @18
    wcel
    #
    @66
    @68
    @53
    @69
    @18
    @68
    @8
    cY
    wcel
    @53
    @69
    wceq
    @50
    @16
    cY
    @8
    @62
    sselda
    vy
    @8
    @25
    @69
    cY
    @26
    @23
    @8
    @24
    opeq1
    @26
    eqid
    @8
    @24
    opex
    fvmpt
    syl
    eleq1d
    @65
    @70
    vw
    @24
    vx
    vex
    vw
    vx
    weq
    @64
    @69
    @18
    @11
    @24
    @8
    opeq2
    eleq1d
    ralsn
    syl6bbr
    ralbidva
    @48
    vt
    vv
    wel
    #
    vt
    @47
    wral
    @67
    vt
    @47
    @18
    dfss3
    @71
    @65
    vt
    vz
    vw
    @16
    @46
    vt
    cv
    @64
    @18
    eleq1
    ralxp
    bitri
    syl6bbr
    3bitrd
    rabbidva
    @43
    @49
    cR
    wcel
    #
    vw
    vr
    wel
    #
    vr
    cv
    #
    @49
    wss
    #
    wa
    #
    vr
    cR
    wrex
    #
    vw
    @49
    wral
    #
    @43
    @77
    vw
    @49
    @11
    @49
    wcel
    @43
    @11
    cX
    wcel
    #
    @16
    @11
    csn
    #
    cxp
    #
    @18
    wss
    #
    wa
    #
    @77
    @48
    @82
    vx
    @11
    cX
    vx
    vw
    weq
    #
    @47
    @81
    @18
    @84
    @46
    @80
    @16
    @24
    @11
    sneq
    xpeq2d
    sseq1d
    elrab
    @43
    @83
    wa
    #
    @77
    @73
    @31
    cuni
    #
    @74
    cxp
    #
    @18
    @16
    cX
    cxp
    #
    cin
    #
    wss
    #
    wa
    #
    vr
    cR
    wrex
    @85
    vr
    @11
    @31
    cR
    @89
    @86
    cR
    cuni
    #
    @86
    eqid
    @92
    eqid
    #
    @42
    @32
    @83
    simplr
    @85
    @1
    cR
    ctop
    wcel
    #
    @42
    @1
    @32
    @83
    @1
    @2
    @41
    simpll
    ad2antrr
    #
    cX
    cR
    topontop
    #
    syl
    #
    @85
    @89
    @4
    @88
    crest
    co
    #
    @31
    cR
    ctx
    co
    #
    @85
    @4
    ctop
    wcel
    #
    @88
    cvv
    wcel
    #
    @40
    @89
    @98
    wcel
    @3
    @100
    @41
    @32
    @83
    @3
    cS
    ctop
    wcel
    #
    @94
    @100
    @2
    @102
    @1
    cY
    cS
    topontop
    adantl
    #
    @1
    @94
    @2
    @96
    adantr
    #
    cS
    cR
    txtop
    syl2anc
    #
    ad3antrrr
    @85
    @16
    cvv
    wcel
    #
    cX
    cR
    wcel
    #
    @101
    vk
    vex
    #
    @85
    @1
    @107
    @95
    cX
    cR
    toponmax
    syl
    #
    @16
    cX
    cvv
    cR
    xpexg
    sylancr
    @42
    @40
    @32
    @83
    @3
    @39
    @40
    simprr
    ad2antrr
    @18
    @88
    @4
    ctop
    cvv
    elrestr
    syl3anc
    @85
    @98
    @31
    cR
    cX
    crest
    co
    #
    ctx
    co
    #
    @99
    @85
    @102
    @94
    @106
    @107
    @98
    @111
    wceq
    @3
    @102
    @41
    @32
    @83
    @103
    ad3antrrr
    @97
    @106
    @85
    @108
    a1i
    @109
    @16
    cX
    cS
    cR
    ctop
    ctop
    cvv
    cR
    txrest
    syl22anc
    @85
    @110
    cR
    @31
    ctx
    @85
    @110
    cR
    @92
    crest
    co
    #
    cR
    @85
    cX
    @92
    cR
    crest
    @85
    @1
    cX
    @92
    wceq
    @95
    cX
    cR
    toponuni
    syl
    #
    oveq2d
    @85
    @1
    @112
    cR
    wceq
    @95
    cR
    @0
    @92
    @93
    restid
    syl
    eqtrd
    oveq2d
    eqtrd
    eleqtrd
    @85
    @86
    @80
    cxp
    @81
    @89
    @85
    @16
    @86
    @80
    @85
    @31
    @16
    ctopon
    cfv
    wcel
    #
    @16
    @86
    wceq
    #
    @85
    @2
    @59
    @114
    @43
    @2
    @83
    @60
    adantr
    @43
    @59
    @83
    @61
    adantr
    @16
    cS
    cY
    resttopon
    syl2anc
    @16
    @31
    toponuni
    syl
    #
    xpeq1d
    @85
    @81
    @18
    @88
    @43
    @79
    @82
    simprr
    @85
    @80
    cX
    wss
    @81
    @88
    wss
    @85
    @11
    cX
    @43
    @79
    @82
    simprl
    #
    snssd
    @80
    cX
    @16
    xpss2
    syl
    ssind
    eqsstr3d
    @85
    @11
    cX
    @92
    @117
    @113
    eleqtrd
    txtube
    @85
    @76
    @91
    vr
    cR
    @85
    @74
    cR
    wcel
    #
    wa
    #
    @75
    @90
    @73
    @119
    @75
    @48
    vx
    @74
    wral
    #
    @16
    @74
    cxp
    #
    @89
    wss
    #
    @90
    @119
    @74
    cX
    wss
    #
    @75
    @120
    wb
    @85
    @1
    @118
    @123
    @95
    @74
    cR
    cX
    toponss
    sylan
    #
    @75
    @123
    @120
    @48
    vx
    cX
    @74
    ssrab
    baib
    syl
    @119
    @121
    @18
    wss
    #
    @125
    @121
    @88
    wss
    #
    wa
    @120
    @122
    @119
    @126
    @125
    @119
    @123
    @126
    @124
    @74
    cX
    @16
    xpss2
    syl
    biantrud
    @125
    vx
    @74
    @47
    ciun
    #
    @18
    wss
    @120
    @121
    @127
    @18
    @16
    vx
    @74
    @46
    ciun
    #
    cxp
    @121
    @127
    @128
    @74
    @16
    vx
    @74
    iunid
    xpeq2i
    vx
    @74
    @46
    @16
    xpiundi
    eqtr3i
    sseq1i
    vx
    @74
    @47
    @18
    iunss
    bitri
    @121
    @18
    @88
    ssin
    3bitr3g
    @119
    @121
    @87
    @89
    @119
    @16
    @86
    @74
    @85
    @115
    @118
    @116
    adantr
    xpeq1d
    sseq1d
    3bitrd
    anbi2d
    rexbidva
    mpbird
    sylan2b
    ralrimiva
    @43
    @3
    @94
    @72
    @78
    wb
    @57
    @104
    vw
    vr
    @49
    cR
    eltop2
    3syl
    mpbird
    eqeltrd
    @33
    @9
    @45
    cR
    @33
    @9
    @7
    @20
    cima
    @45
    @8
    @20
    @7
    imaeq2
    vx
    cX
    @26
    @20
    cF
    xkoinjcn.3
    mptpreima
    syl6eq
    eleq1d
    syl5ibrcom
    expimpd
    rexlimdvva
    syl5bi
    ralrimiv
    @3
    vz
    @22
    cF
    cR
    @5
    cvv
    cX
    @6
    @1
    @2
    simpl
    @22
    cvv
    wcel
    @3
    @22
    @6
    cpw
    #
    @6
    cS
    @4
    ccn
    ovex
    pwex
    @14
    @4
    cxp
    #
    @129
    @21
    wf
    @22
    @129
    wss
    vw
    vv
    cS
    @4
    @21
    vf
    vk
    @14
    @12
    @36
    @37
    @38
    xkotf
    @130
    @129
    @21
    frn
    ax-mp
    ssexi
    a1i
    @3
    @102
    @100
    @5
    @22
    cfi
    cfv
    ctg
    cfv
    wceq
    @103
    @105
    vw
    vv
    cS
    @4
    @21
    vf
    vk
    @14
    @12
    @36
    @37
    @38
    xkoval
    syl2anc
    @3
    @102
    @100
    @5
    @6
    ctopon
    cfv
    wcel
    @103
    @105
    cS
    @4
    @5
    @5
    eqid
    xkotopon
    syl2anc
    subbascn
    mpbir2and
end
