include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "cixp.mm"
include "wcel.mm"
include "cdif.mm"
include "ciin.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfel.mm"
include "nfan.mm"
include "cmnf.mm"
include "cioo.mm"
include "cr.mm"
include "cif.mm"
include "wfn.mm"
include "ixpfn.mm"
include "ad2antlr.mm"
include "wss.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "eqimss.mm"
include "syl.mm"
include "wn.mm"
include "ioossre.mm"
include "iffalse.mm"
include "syl5sseqr.mm"
include "pm2.61i.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "adantlr.mm"
include "icossre.mm"
include "syl2anc.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq12d.mm"
include "fvixp.mm"
include "adantll.mm"
include "sseldd.mm"
include "mnfltd.mm"
include "clt.mm"
include "wbr.mm"
include "icoltub.mm"
include "syl3anc.mm"
include "eliood.mm"
include "sseldi.mm"
include "ralrimiva.mm"
include "jca.mm"
include "vex.mm"
include "elixp.mm"
include "sylibr.mm"
include "cfn.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "equequ1.mm"
include "ifbid.mm"
include "cbvixpv.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "adantr.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "hspval.mm"
include "eleqtrrd.mm"
include "eleqtrd.mm"
include "iooltub.mm"
include "adantllr.mm"
include "cle.mm"
include "biimpi.mm"
include "simprd.mm"
include "rspa.mm"
include "sylan.mm"
include "icogelb.mm"
include "lenltd.mm"
include "mpbid.mm"
include "pm2.65da.mm"
include "eldifd.mm"
include "ex.mm"
include "ralrimi.mm"
include "cvv.mm"
include "eliin.mm"
include "ax-mp.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "id.mm"
include "difeq12d.mm"
include "eleq2d.mm"
include "eliind.mm"
include "eldifad.mm"
include "ad2antrr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "nfii1.mm"
include "simpll.mm"
include "eldifi.mm"
include "simplr.mm"
include "syl21anc.mm"
include "adantl.mm"
include "ad4ant13.mm"
include "eqeltrd.mm"
include "eqcomd.mm"
include "syl6eqss.mm"
include "ssid.mm"
include "fvixp2.mm"
include "pm2.61dan.mm"
include "eldifn.mm"
include "ad3antlr.mm"
include "mpbird.mm"
include "elicod.mm"
include "impbid.mm"
include "alrimiv.mm"
include "dfcleq.mm"

theorem hspdifhsp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vi: setvar i
  let cH: class H
  let cX: class X
  let vl: setvar l
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  assume hspdifhsp.x: |- ( ph -> X e. Fin )
  assume hspdifhsp.n: |- ( ph -> X =/= (/) )
  assume hspdifhsp.a: |- ( ph -> A : X --> RR )
  assume hspdifhsp.b: |- ( ph -> B : X --> RR )
  assume hspdifhsp.h: |- H = ( x e. Fin |-> ( l e. x , y e. RR |-> X_ i e. x if ( i = l , ( -oo (,) y ) , RR ) ) )

  disjoint A i
  disjoint A l
  disjoint A x
  disjoint A y
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B i
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint H i
  disjoint H l
  disjoint H x
  disjoint H y
  disjoint X i
  disjoint X l
  disjoint X x
  disjoint X y
  disjoint i ph
  disjoint l ph
  disjoint ph x
  disjoint ph y
  disjoint A f
  disjoint A h
  disjoint A k
  disjoint f h
  disjoint f i
  disjoint f k
  disjoint f l
  disjoint f x
  disjoint f y
  disjoint h i
  disjoint h k
  disjoint h l
  disjoint h x
  disjoint h y
  disjoint i k
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint B f
  disjoint B h
  disjoint B k
  disjoint H f
  disjoint H h
  disjoint H k
  disjoint X f
  disjoint X h
  disjoint X k
  disjoint f ph
  disjoint h ph
  disjoint k ph
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) [,) ( B ` i ) ) = |^|_ i e. X ( ( i ( H ` X ) ( B ` i ) ) \ ( i ( H ` X ) ( A ` i ) ) ) )

  proof
    wph
    vf
    cv
    #
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    cico
    co
    #
    cixp
    #
    wcel
    #
    @0
    vi
    cX
    @1
    @3
    cX
    cH
    cfv
    #
    co
    #
    @1
    @2
    @7
    co
    #
    cdif
    #
    ciin
    #
    wcel
    #
    wb
    #
    vf
    wal
    @5
    @11
    wceq
    wph
    @13
    vf
    wph
    @6
    @12
    wph
    @6
    @12
    wph
    @6
    wa
    #
    @0
    @10
    wcel
    #
    vi
    cX
    wral
    #
    @12
    @14
    @15
    vi
    cX
    wph
    @6
    vi
    wph
    vi
    nfv
    #
    vi
    @0
    @5
    vi
    @0
    nfcv
    #
    vi
    cX
    @4
    nfixp1
    nfel
    nfan
    @14
    @1
    cX
    wcel
    #
    @15
    @14
    @19
    wa
    #
    @0
    @8
    @9
    @20
    @0
    vk
    cX
    vk
    cv
    #
    @1
    wceq
    #
    cmnf
    @3
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    @8
    @20
    @0
    cX
    wfn
    #
    @21
    @0
    cfv
    #
    @24
    wcel
    #
    vk
    cX
    wral
    #
    wa
    @0
    @25
    wcel
    #
    @20
    @26
    @29
    @6
    @26
    wph
    @19
    vi
    cX
    @4
    @0
    ixpfn
    ad2antlr
    @20
    @28
    vk
    cX
    @14
    @21
    cX
    wcel
    #
    @28
    @19
    @14
    @31
    wa
    #
    cmnf
    @21
    cB
    cfv
    #
    cioo
    co
    #
    @24
    @27
    @22
    @34
    @24
    wss
    #
    @22
    @34
    @24
    wceq
    @35
    @22
    @34
    @23
    @24
    @22
    @33
    @3
    cmnf
    cioo
    @21
    @1
    cB
    fveq2
    oveq2d
    @22
    @23
    cr
    iftrue
    #
    eqtr4d
    @34
    @24
    eqimss
    syl
    @22
    wn
    #
    cr
    @34
    @24
    cmnf
    @33
    ioossre
    @22
    @23
    cr
    iffalse
    #
    syl5sseqr
    pm2.61i
    @32
    cmnf
    @33
    @27
    cmnf
    cxr
    wcel
    #
    @32
    mnfxr
    a1i
    wph
    @31
    @33
    cxr
    wcel
    #
    @6
    wph
    @31
    wa
    #
    @33
    wph
    cX
    cr
    @21
    cB
    hspdifhsp.b
    ffvelrnda
    #
    rexrd
    #
    adantlr
    #
    @32
    @21
    cA
    cfv
    #
    @33
    cico
    co
    #
    cr
    @27
    wph
    @31
    @46
    cr
    wss
    #
    @6
    @41
    @45
    cr
    wcel
    @40
    @47
    wph
    cX
    cr
    @21
    cA
    hspdifhsp.a
    ffvelrnda
    #
    @43
    @45
    @33
    icossre
    syl2anc
    adantlr
    @6
    @31
    @27
    @46
    wcel
    #
    wph
    @6
    @31
    wa
    @6
    @31
    @49
    @6
    @31
    simpl
    @6
    @31
    simpr
    vi
    cX
    @4
    @21
    @46
    @0
    @1
    @21
    wceq
    #
    @2
    @45
    @3
    @33
    cico
    @1
    @21
    cA
    fveq2
    #
    @1
    @21
    cB
    fveq2
    #
    oveq12d
    fvixp
    syl2anc
    adantll
    #
    sseldd
    #
    @32
    @27
    @54
    mnfltd
    @32
    @45
    cxr
    wcel
    #
    @40
    @49
    @27
    @33
    clt
    wbr
    wph
    @31
    @55
    @6
    @41
    @45
    @48
    rexrd
    adantlr
    @44
    @53
    @45
    @33
    @27
    icoltub
    syl3anc
    eliood
    sseldi
    adantlr
    ralrimiva
    jca
    vk
    cX
    @24
    @0
    vf
    vex
    #
    elixp
    sylibr
    wph
    @19
    @8
    @25
    wceq
    #
    @6
    wph
    @19
    wa
    #
    vx
    vy
    vl
    vk
    cH
    @1
    cX
    @3
    cH
    vx
    cfn
    vl
    vy
    vx
    cv
    #
    cr
    vi
    @59
    @1
    vl
    cv
    #
    wceq
    #
    cmnf
    vy
    cv
    #
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    #
    vx
    cfn
    vl
    vy
    @59
    cr
    vk
    @59
    @21
    @60
    wceq
    #
    @63
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    hspdifhsp.h
    vx
    cfn
    @66
    @71
    vl
    vy
    @59
    cr
    @65
    @70
    @65
    @70
    wceq
    @60
    @59
    wcel
    @62
    cr
    wcel
    wa
    #
    vi
    vk
    @59
    @64
    @69
    @50
    @61
    @68
    @63
    cr
    vi
    vk
    vl
    equequ1
    ifbid
    cbvixpv
    a1i
    mpt2eq3ia
    mpteq2i
    eqtri
    #
    wph
    cX
    cfn
    wcel
    #
    @19
    hspdifhsp.x
    adantr
    #
    wph
    @19
    simpr
    #
    @58
    cX
    cr
    @1
    cB
    wph
    cX
    cr
    cB
    wf
    @19
    hspdifhsp.b
    adantr
    @76
    ffvelrnd
    #
    hspval
    #
    adantlr
    eleqtrrd
    @20
    @0
    @9
    wcel
    #
    @1
    @0
    cfv
    #
    @2
    clt
    wbr
    #
    wph
    @19
    @79
    @81
    @6
    @58
    @79
    wa
    #
    @39
    @2
    cxr
    wcel
    #
    @80
    cmnf
    @2
    cioo
    co
    #
    wcel
    #
    @81
    @39
    @82
    mnfxr
    a1i
    @58
    @83
    @79
    @58
    @2
    @58
    cX
    cr
    @1
    cA
    wph
    cX
    cr
    cA
    wf
    @19
    hspdifhsp.a
    adantr
    @76
    ffvelrnd
    #
    rexrd
    #
    adantr
    @82
    @0
    vk
    cX
    @22
    @84
    cr
    cif
    #
    cixp
    #
    wcel
    #
    @19
    @85
    @82
    @0
    @9
    @89
    @58
    @79
    simpr
    @58
    @9
    @89
    wceq
    @79
    @58
    vx
    vy
    vl
    vk
    cH
    @1
    cX
    @2
    @73
    @75
    @76
    @86
    hspval
    #
    adantr
    eleqtrd
    @58
    @19
    @79
    @76
    adantr
    vk
    cX
    @88
    @1
    @84
    @0
    @22
    @84
    cr
    iftrue
    #
    fvixp
    syl2anc
    cmnf
    @2
    @80
    iooltub
    syl3anc
    adantllr
    @20
    @81
    wn
    #
    @79
    @20
    @2
    @80
    cle
    wbr
    #
    @93
    @20
    @83
    @3
    cxr
    wcel
    #
    @80
    @4
    wcel
    #
    @94
    wph
    @19
    @83
    @6
    @87
    adantlr
    wph
    @19
    @95
    @6
    @58
    @3
    @77
    rexrd
    #
    adantlr
    @6
    @19
    @96
    wph
    @6
    @96
    vi
    cX
    wral
    #
    @19
    @96
    @6
    @26
    @98
    @6
    @26
    @98
    wa
    #
    vi
    cX
    @4
    @0
    @56
    elixp
    #
    biimpi
    simprd
    @96
    vi
    cX
    rspa
    sylan
    adantll
    #
    @2
    @3
    @80
    icogelb
    syl3anc
    @20
    @2
    @80
    wph
    @19
    @2
    cr
    wcel
    #
    @6
    @86
    adantlr
    @20
    @4
    cr
    @80
    wph
    @19
    @4
    cr
    wss
    #
    @6
    @58
    @102
    @95
    @103
    @86
    @97
    @2
    @3
    icossre
    syl2anc
    adantlr
    @101
    sseldd
    lenltd
    mpbid
    adantr
    pm2.65da
    eldifd
    ex
    ralrimi
    @0
    cvv
    wcel
    @12
    @16
    wb
    @56
    vi
    @0
    cX
    @10
    cvv
    eliin
    ax-mp
    #
    sylibr
    ex
    wph
    @12
    @6
    wph
    @12
    wa
    #
    @99
    @6
    @105
    @26
    @98
    @105
    @31
    vk
    wex
    #
    @26
    wph
    @106
    @12
    wph
    cX
    c0
    wne
    #
    @106
    hspdifhsp.n
    @107
    @106
    vk
    cX
    n0
    biimpi
    syl
    adantr
    @105
    @31
    @26
    vk
    @105
    @31
    @26
    @105
    @31
    wa
    #
    @0
    vh
    cX
    vh
    cv
    #
    @21
    wceq
    @34
    cr
    cif
    #
    cixp
    #
    wcel
    @26
    @108
    @0
    @21
    @33
    @7
    co
    #
    @111
    @12
    @31
    @0
    @112
    wcel
    wph
    @12
    @31
    wa
    #
    @0
    @112
    @21
    @45
    @7
    co
    #
    @113
    vi
    @0
    cX
    @10
    @112
    @114
    cdif
    #
    @21
    @12
    @31
    simpl
    @12
    @31
    simpr
    @50
    @10
    @115
    @0
    @50
    @8
    @112
    @9
    @114
    @50
    @1
    @21
    @3
    @33
    @7
    @50
    id
    #
    @52
    oveq12d
    @50
    @1
    @21
    @2
    @45
    @7
    @116
    @51
    oveq12d
    difeq12d
    eleq2d
    eliind
    eldifad
    adantll
    @108
    vx
    vy
    vl
    vh
    cH
    @21
    cX
    @33
    cH
    @67
    vx
    cfn
    vl
    vy
    @59
    cr
    vh
    @59
    @109
    @60
    wceq
    #
    @63
    cr
    cif
    #
    cixp
    #
    cmpt2
    #
    cmpt
    hspdifhsp.h
    vx
    cfn
    @66
    @120
    vl
    vy
    @59
    cr
    @65
    @119
    @65
    @119
    wceq
    @72
    vi
    vh
    @59
    @64
    @118
    @1
    @109
    wceq
    @61
    @117
    @63
    cr
    vi
    vh
    vl
    equequ1
    ifbid
    cbvixpv
    a1i
    mpt2eq3ia
    mpteq2i
    eqtri
    wph
    @74
    @12
    @31
    hspdifhsp.x
    ad2antrr
    @105
    @31
    simpr
    wph
    @31
    @33
    cr
    wcel
    @12
    @42
    adantlr
    hspval
    eleqtrd
    vh
    cX
    @110
    @0
    ixpfn
    syl
    ex
    exlimdv
    mpd
    @105
    @96
    vi
    cX
    wph
    @12
    vi
    @17
    vi
    @0
    @11
    @18
    vi
    cX
    @10
    nfii1
    nfel
    nfan
    @105
    @19
    @96
    @105
    @19
    wa
    wph
    @15
    @19
    @96
    wph
    @12
    @19
    simpll
    @12
    @19
    @15
    wph
    @12
    @19
    wa
    @16
    @19
    @15
    @12
    @16
    @19
    @12
    @16
    @104
    biimpi
    adantr
    @12
    @19
    simpr
    @15
    vi
    cX
    rspa
    syl2anc
    adantll
    @105
    @19
    simpr
    wph
    @15
    wa
    #
    @19
    wa
    #
    @2
    @3
    @80
    wph
    @19
    @83
    @15
    @87
    adantlr
    wph
    @19
    @95
    @15
    @97
    adantlr
    @122
    @80
    @122
    wph
    @0
    @8
    wcel
    #
    @19
    @80
    cr
    wcel
    #
    wph
    @15
    @19
    simpll
    #
    @15
    @123
    wph
    @19
    @0
    @8
    @9
    eldifi
    #
    ad2antlr
    #
    @121
    @19
    simpr
    #
    wph
    @123
    wa
    #
    @19
    wa
    #
    @23
    cr
    @80
    cmnf
    @3
    ioossre
    #
    @130
    @30
    @19
    @80
    @23
    wcel
    #
    @130
    @0
    @8
    @25
    wph
    @123
    @19
    simplr
    wph
    @19
    @57
    @123
    @78
    adantlr
    eleqtrd
    #
    @129
    @19
    simpr
    vk
    cX
    @24
    @1
    @23
    @0
    @36
    fvixp
    syl2anc
    #
    sseldi
    #
    syl21anc
    #
    rexrd
    @122
    @94
    @93
    @122
    @81
    @79
    @122
    @81
    wa
    @129
    @19
    @81
    @79
    @121
    @129
    @19
    @81
    @121
    wph
    @123
    wph
    @15
    simpl
    @15
    @123
    wph
    @126
    adantl
    jca
    ad2antrr
    @121
    @19
    @81
    simplr
    @122
    @81
    simpr
    @130
    @81
    wa
    #
    @0
    @89
    @9
    @137
    @26
    @27
    @88
    wcel
    #
    vk
    cX
    wral
    #
    wa
    @90
    @137
    @26
    @139
    @130
    @26
    @81
    @130
    @30
    @26
    @133
    vk
    cX
    @24
    @0
    ixpfn
    syl
    adantr
    @137
    @138
    vk
    cX
    @137
    @31
    wa
    #
    @22
    @138
    @140
    @22
    wa
    @27
    @84
    @88
    @137
    @22
    @27
    @84
    wcel
    @31
    @137
    @22
    wa
    @27
    @80
    @84
    @22
    @27
    @80
    wceq
    @137
    @21
    @1
    @0
    fveq2
    adantl
    @137
    @85
    @22
    @137
    cmnf
    @2
    @80
    @39
    @137
    mnfxr
    a1i
    wph
    @19
    @83
    @123
    @81
    @87
    ad4ant13
    @130
    @124
    @81
    @135
    adantr
    #
    @137
    @80
    @141
    mnfltd
    @130
    @81
    simpr
    eliood
    adantr
    eqeltrd
    adantlr
    @22
    @84
    @88
    wceq
    @140
    @22
    @88
    @84
    @92
    eqcomd
    adantl
    eleqtrd
    @130
    @31
    @37
    @138
    @81
    @130
    @31
    wa
    #
    @37
    wa
    @27
    cr
    @88
    @142
    @27
    cr
    wcel
    @37
    @142
    @24
    cr
    @27
    @22
    @24
    cr
    wss
    @22
    @24
    @23
    cr
    @36
    @131
    syl6eqss
    @37
    @24
    cr
    cr
    @38
    cr
    ssid
    syl6eqss
    pm2.61i
    @142
    @30
    @31
    @28
    @130
    @30
    @31
    @133
    adantr
    @130
    @31
    simpr
    vk
    cX
    @24
    @0
    fvixp2
    syl2anc
    sseldi
    adantr
    @37
    cr
    @88
    wceq
    @142
    @37
    @88
    cr
    @22
    @84
    cr
    iffalse
    eqcomd
    adantl
    eleqtrd
    adantllr
    pm2.61dan
    ralrimiva
    jca
    vk
    cX
    @88
    @0
    @56
    elixp
    sylibr
    wph
    @19
    @89
    @9
    wceq
    @123
    @81
    @58
    @9
    @89
    @91
    eqcomd
    ad4ant13
    eleqtrd
    syl21anc
    @15
    @79
    wn
    wph
    @19
    @81
    @0
    @8
    @9
    eldifn
    ad3antlr
    pm2.65da
    @122
    @2
    @80
    @122
    wph
    @19
    @102
    @125
    @128
    @86
    syl2anc
    @136
    lenltd
    mpbird
    @122
    wph
    @123
    @19
    @80
    @3
    clt
    wbr
    #
    @125
    @127
    @128
    @130
    @39
    @95
    @132
    @143
    @39
    @130
    mnfxr
    a1i
    wph
    @19
    @95
    @123
    @97
    adantlr
    @134
    cmnf
    @3
    @80
    iooltub
    syl3anc
    syl21anc
    elicod
    syl21anc
    ex
    ralrimi
    jca
    @100
    sylibr
    ex
    impbid
    alrimiv
    vf
    @5
    @11
    dfcleq
    sylibr
end
