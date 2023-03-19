include "cuni.mm"
include "cfv.mm"
include "cres.mm"
include "csumge0.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "cv.mm"
include "ciun.mm"
include "cmpt.mm"
include "cpw.mm"
include "wf.mm"
include "id.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wcel.mm"
include "cif.mm"
include "wa.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "fssd.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "iffalse.mm"
include "0ex.mm"
include "snid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "pm2.61dan.mm"
include "fmptd.mm"
include "0elpw.mm"
include "snssi.mm"
include "unssd.mm"
include "wi.mm"
include "cvv.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "feq1.mm"
include "anbi2d.mm"
include "fveq1.mm"
include "iuneq2d.mm"
include "fveq2d.mm"
include "simpl.mm"
include "fveq1d.mm"
include "mpteq2dva.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtocl.mm"
include "syl2anc.mm"
include "wfo.mm"
include "wrex.mm"
include "wral.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqcomd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "wb.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "feq1d.mm"
include "mpbird.mm"
include "f1ofo.mm"
include "dffo3.mm"
include "sylib.mm"
include "simprd.mm"
include "rspa.mm"
include "nfv.mm"
include "nfre1.mm"
include "w3a.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt2.mm"
include "3ad2ant3.mm"
include "3eqtrrd.mm"
include "3adant1l.mm"
include "rspe.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "sylibr.mm"
include "founiiun.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtrri.mm"
include "wex.mm"
include "wpss.mm"
include "wne.mm"
include "necon3bi.mm"
include "df-pss.mm"
include "pssnel.mm"
include "simprl.mm"
include "ad2antll.mm"
include "ad2antlr.mm"
include "ex.mm"
include "exlimd.mm"
include "simplll.mm"
include "elsni.mm"
include "con3i.mm"
include "elunnel2.mm"
include "foelrni.mm"
include "sselda.mm"
include "sylancl.mm"
include "simp3.mm"
include "eqtr2d.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "uncom.mm"
include "undif.mm"
include "mpteq1d.mm"
include "difexg.mm"
include "ssexd.mm"
include "cin.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "eldifi.mm"
include "syldan.mm"
include "sge0splitmpt.mm"
include "sge0xrcl.mm"
include "xaddid2d.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "sge0z.mm"
include "oveq1d.mm"
include "feqresmpt.mm"
include "fveq2.mm"
include "sge0f1o.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem isomenndlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cO: class O
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x
  assume isomenndlem.o: |- ( ph -> O : ~P X --> ( 0 [,] +oo ) )
  assume isomenndlem.o0: |- ( ph -> ( O ` (/) ) = 0 )
  assume isomenndlem.y: |- ( ph -> Y C_ ~P X )
  assume isomenndlem.subadd: |- ( ( ph /\ a : NN --> ~P X ) -> ( O ` U_ n e. NN ( a ` n ) ) <_ ( sum^ ` ( n e. NN |-> ( O ` ( a ` n ) ) ) ) )
  assume isomenndlem.b: |- ( ph -> B C_ NN )
  assume isomenndlem.f: |- ( ph -> F : B -1-1-onto-> Y )
  assume isomenndlem.a: |- A = ( n e. NN |-> if ( n e. B , ( F ` n ) , (/) ) )

  disjoint A a
  disjoint A n
  disjoint a n
  disjoint B n
  disjoint F n
  disjoint O a
  disjoint O n
  disjoint X a
  disjoint Y n
  disjoint a ph
  disjoint n ph
  disjoint A y
  disjoint n y
  disjoint B y
  disjoint F y
  disjoint O y
  disjoint X y
  disjoint Y y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( O ` U. Y ) <_ ( sum^ ` ( O |` Y ) ) )

  proof
    wph
    cY
    cuni
    #
    cO
    cfv
    #
    cO
    cY
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    vn
    cn
    vn
    cv
    #
    cA
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    vn
    cn
    @5
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wph
    wph
    cn
    cX
    cpw
    #
    cA
    wf
    #
    @11
    wph
    id
    wph
    cn
    cY
    c0
    csn
    #
    cun
    #
    @12
    cA
    wph
    vn
    cn
    @4
    cB
    wcel
    #
    @4
    cF
    cfv
    #
    c0
    cif
    #
    @15
    cA
    wph
    @4
    cn
    wcel
    #
    wa
    #
    @16
    @18
    @15
    wcel
    #
    wph
    @16
    @21
    @19
    wph
    @16
    wa
    #
    @18
    @17
    @15
    @16
    @18
    @17
    wceq
    #
    wph
    @16
    @17
    c0
    iftrue
    #
    adantl
    #
    wph
    cB
    @15
    @4
    cF
    wph
    cB
    cY
    @15
    cF
    wph
    cB
    cY
    cF
    wf1o
    #
    cB
    cY
    cF
    wf
    #
    isomenndlem.f
    cB
    cY
    cF
    f1of
    syl
    #
    cY
    @15
    wss
    wph
    cY
    @14
    ssun1
    a1i
    fssd
    ffvelrnda
    eqeltrd
    adantlr
    wph
    @16
    wn
    #
    @21
    @19
    wph
    @29
    wa
    #
    @18
    c0
    @15
    @29
    @18
    c0
    wceq
    #
    wph
    @16
    @17
    c0
    iffalse
    #
    adantl
    c0
    @15
    wcel
    #
    @30
    c0
    @14
    wcel
    @33
    c0
    0ex
    snid
    c0
    @14
    cY
    elun2
    ax-mp
    a1i
    eqeltrd
    adantlr
    pm2.61dan
    isomenndlem.a
    fmptd
    #
    wph
    cY
    @14
    @12
    isomenndlem.y
    @14
    @12
    wss
    #
    wph
    c0
    @12
    wcel
    @35
    cX
    0elpw
    c0
    @12
    snssi
    ax-mp
    a1i
    unssd
    fssd
    #
    wph
    cn
    @12
    va
    cv
    #
    wf
    #
    wa
    #
    vn
    cn
    @4
    @37
    cfv
    #
    ciun
    #
    cO
    cfv
    #
    vn
    cn
    @40
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    wph
    @13
    wa
    #
    @11
    wi
    va
    cA
    cA
    vn
    cn
    @18
    cmpt
    #
    cvv
    isomenndlem.a
    vn
    cn
    @18
    nnex
    mptex
    eqeltri
    @37
    cA
    wceq
    #
    @39
    @47
    @46
    @11
    @49
    @38
    @13
    wph
    cn
    @12
    @37
    cA
    feq1
    anbi2d
    @49
    @42
    @7
    @45
    @10
    cle
    @49
    @41
    @6
    cO
    @49
    vn
    cn
    @40
    @5
    @4
    @37
    cA
    fveq1
    iuneq2d
    fveq2d
    @49
    @44
    @9
    csumge0
    @49
    vn
    cn
    @43
    @8
    @49
    @19
    wa
    #
    @40
    @5
    cO
    @50
    @4
    @37
    cA
    @49
    @19
    simpl
    fveq1d
    fveq2d
    mpteq2dva
    fveq2d
    breq12d
    imbi12d
    isomenndlem.subadd
    vtocl
    syl2anc
    wph
    @1
    @7
    @3
    @10
    cle
    wph
    @0
    @6
    cO
    wph
    cB
    cn
    wceq
    #
    @0
    @6
    wceq
    #
    wph
    @51
    wa
    #
    cn
    cY
    cA
    wfo
    #
    @52
    @53
    cn
    cY
    cA
    wf
    #
    vy
    cv
    #
    @5
    wceq
    #
    vn
    cn
    wrex
    #
    vy
    cY
    wral
    #
    wa
    @54
    @53
    @55
    @59
    @53
    @55
    cn
    cY
    vn
    cn
    @17
    cmpt
    #
    wf
    #
    @53
    vn
    cn
    @17
    cY
    @60
    @53
    @19
    wa
    cB
    cY
    @4
    cF
    wph
    @27
    @51
    @19
    @28
    ad2antrr
    @51
    @19
    @16
    wph
    @51
    @19
    wa
    #
    @4
    cn
    cB
    @51
    @19
    simpr
    @51
    cn
    cB
    wceq
    @19
    @51
    cB
    cn
    @51
    id
    #
    eqcomd
    adantr
    eleqtrd
    #
    adantll
    ffvelrnd
    @60
    eqid
    fmptd
    @51
    @55
    @61
    wb
    wph
    @51
    cn
    cY
    cA
    @60
    @51
    cA
    @48
    @60
    cA
    @48
    wceq
    @51
    isomenndlem.a
    a1i
    #
    @51
    vn
    cn
    @18
    @17
    @62
    @16
    @17
    c0
    @64
    iftrued
    mpteq2dva
    eqtrd
    feq1d
    adantl
    mpbird
    @53
    @58
    vy
    cY
    @53
    @56
    cY
    wcel
    #
    wa
    @56
    @17
    wceq
    #
    vn
    cB
    wrex
    #
    @58
    wph
    @66
    @68
    @51
    wph
    @66
    wa
    #
    @68
    vy
    cY
    wral
    #
    @66
    @68
    wph
    @70
    @66
    wph
    @27
    @70
    wph
    cB
    cY
    cF
    wfo
    #
    @27
    @70
    wa
    wph
    @26
    @71
    isomenndlem.f
    cB
    cY
    cF
    f1ofo
    syl
    #
    vn
    vy
    cB
    cY
    cF
    dffo3
    sylib
    simprd
    adantr
    wph
    @66
    simpr
    #
    @68
    vy
    cY
    rspa
    syl2anc
    adantlr
    @53
    @68
    @58
    wi
    @66
    @53
    @67
    @58
    vn
    cB
    @53
    vn
    nfv
    @57
    vn
    cn
    nfre1
    #
    @53
    @16
    @67
    @58
    @53
    @16
    @67
    w3a
    @19
    @57
    @58
    @53
    @16
    @19
    @67
    @51
    @16
    @19
    wph
    @51
    @16
    wa
    #
    @4
    cB
    cn
    @51
    @16
    simpr
    @51
    @16
    simpl
    eleqtrd
    #
    adantll
    3adant3
    @51
    @16
    @67
    @57
    wph
    @51
    @16
    @67
    w3a
    @5
    @4
    @48
    cfv
    #
    @17
    @56
    @51
    @16
    @5
    @77
    wceq
    @67
    @51
    @4
    cA
    @48
    @65
    fveq1d
    3ad2ant1
    @51
    @16
    @77
    @17
    wceq
    @67
    @75
    @77
    @18
    @17
    @75
    @19
    @18
    cvv
    wcel
    #
    @77
    @18
    wceq
    @76
    @78
    @75
    @16
    @17
    c0
    @4
    cF
    fvex
    0ex
    ifex
    #
    a1i
    vn
    cn
    @18
    cvv
    @48
    @48
    eqid
    fvmpt2
    syl2anc
    @16
    @23
    @51
    @24
    adantl
    eqtrd
    3adant3
    @67
    @51
    @17
    @56
    wceq
    #
    @16
    @67
    @56
    @17
    @67
    id
    eqcomd
    3ad2ant3
    3eqtrrd
    3adant1l
    @57
    vn
    cn
    rspe
    #
    syl2anc
    3exp
    rexlimd
    adantr
    mpd
    ralrimiva
    jca
    vn
    vy
    cn
    cY
    cA
    dffo3
    sylibr
    vn
    cn
    cY
    cA
    founiiun
    syl
    wph
    @51
    wn
    #
    wa
    #
    @0
    @15
    cuni
    #
    @6
    @0
    @84
    wceq
    @83
    @84
    @0
    @14
    cuni
    #
    cun
    @0
    c0
    cun
    @0
    cY
    @14
    uniun
    @85
    c0
    @0
    c0
    0ex
    unisn
    uneq2i
    @0
    un0
    3eqtrri
    a1i
    @83
    cn
    @15
    cA
    wfo
    #
    @84
    @6
    wceq
    @83
    cn
    @15
    cA
    wf
    #
    @58
    vy
    @15
    wral
    #
    wa
    @86
    @83
    @87
    @88
    wph
    @87
    @82
    @34
    adantr
    @83
    @58
    vy
    @15
    @83
    @56
    @15
    wcel
    #
    wa
    #
    @56
    c0
    wceq
    #
    @58
    @83
    @91
    @58
    @89
    @83
    @91
    wa
    #
    @19
    @29
    wa
    #
    vn
    wex
    #
    @58
    @83
    @94
    @91
    @83
    cB
    cn
    wpss
    #
    @94
    @83
    cB
    cn
    wss
    #
    cB
    cn
    wne
    #
    wa
    @95
    @83
    @96
    @97
    wph
    @96
    @82
    isomenndlem.b
    adantr
    @82
    @97
    wph
    @51
    cB
    cn
    @63
    necon3bi
    adantl
    jca
    cB
    cn
    df-pss
    sylibr
    vn
    cB
    cn
    pssnel
    syl
    adantr
    @92
    @93
    @58
    vn
    @92
    vn
    nfv
    @74
    wph
    @91
    @93
    @58
    wi
    @82
    wph
    @91
    wa
    #
    @93
    @58
    @98
    @93
    wa
    #
    @19
    @57
    @58
    @98
    @19
    @29
    simprl
    @99
    @5
    @18
    c0
    @56
    wph
    @93
    @5
    @18
    wceq
    #
    @91
    wph
    @93
    wa
    #
    @19
    @78
    @100
    wph
    @19
    @29
    simprl
    @78
    @101
    @79
    a1i
    vn
    cn
    @18
    cvv
    cA
    isomenndlem.a
    fvmpt2
    #
    syl2anc
    adantlr
    @29
    @31
    @98
    @19
    @32
    ad2antll
    @91
    c0
    @56
    wceq
    wph
    @93
    @91
    @56
    c0
    @91
    id
    eqcomd
    ad2antlr
    3eqtrrd
    @81
    syl2anc
    ex
    adantlr
    exlimd
    mpd
    adantlr
    @90
    @91
    wn
    #
    wa
    wph
    @66
    @58
    wph
    @82
    @89
    @103
    simplll
    @89
    @103
    @66
    @83
    @89
    @103
    wa
    @89
    @56
    @14
    wcel
    #
    wn
    #
    @66
    @89
    @103
    simpl
    @103
    @105
    @89
    @104
    @91
    @56
    c0
    elsni
    con3i
    adantl
    @56
    cY
    @14
    elunnel2
    syl2anc
    adantll
    @69
    @80
    vn
    cB
    wrex
    #
    @58
    @69
    @71
    @66
    @106
    wph
    @71
    @66
    @72
    adantr
    @73
    vn
    cB
    cY
    cF
    @56
    foelrni
    syl2anc
    @69
    @80
    @58
    vn
    cB
    @69
    vn
    nfv
    @74
    wph
    @16
    @80
    @58
    wi
    wi
    @66
    wph
    @16
    @80
    @58
    wph
    @16
    @80
    w3a
    #
    @19
    @57
    @58
    wph
    @16
    @19
    @80
    wph
    cB
    cn
    @4
    isomenndlem.b
    sselda
    #
    3adant3
    @107
    @5
    @17
    @56
    wph
    @16
    @5
    @17
    wceq
    @80
    @22
    @5
    @18
    @17
    @22
    @19
    @78
    @100
    @108
    @79
    @102
    sylancl
    @25
    eqtrd
    #
    3adant3
    wph
    @16
    @80
    simp3
    eqtr2d
    @81
    syl2anc
    3exp
    adantr
    rexlimd
    mpd
    syl2anc
    pm2.61dan
    ralrimiva
    jca
    vn
    vy
    cn
    @15
    cA
    dffo3
    sylibr
    vn
    cn
    @15
    cA
    founiiun
    syl
    eqtrd
    pm2.61dan
    fveq2d
    wph
    @10
    vn
    cn
    cB
    cdif
    #
    cB
    cun
    #
    @8
    cmpt
    #
    csumge0
    cfv
    vn
    @110
    @8
    cmpt
    #
    csumge0
    cfv
    #
    vn
    cB
    @8
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    @3
    wph
    @9
    @112
    csumge0
    wph
    vn
    cn
    @111
    @8
    wph
    @111
    cn
    wph
    @111
    cB
    @110
    cun
    #
    cn
    @111
    @118
    wceq
    wph
    @110
    cB
    uncom
    a1i
    wph
    @96
    @118
    cn
    wceq
    isomenndlem.b
    cB
    cn
    undif
    sylib
    eqtrd
    eqcomd
    mpteq1d
    fveq2d
    wph
    vn
    @110
    cB
    @8
    cvv
    cvv
    wph
    vn
    nfv
    #
    @110
    cvv
    wcel
    #
    wph
    cn
    cvv
    wcel
    #
    @120
    nnex
    cn
    cB
    cvv
    difexg
    ax-mp
    a1i
    #
    wph
    cB
    cn
    cvv
    @121
    wph
    nnex
    a1i
    isomenndlem.b
    ssexd
    #
    @110
    cB
    cin
    #
    c0
    wceq
    wph
    @124
    cB
    @110
    cin
    c0
    @110
    cB
    incom
    cB
    cn
    disjdif
    eqtri
    a1i
    wph
    @4
    @110
    wcel
    #
    wa
    #
    wph
    @19
    @8
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @125
    simpl
    #
    @125
    @19
    wph
    @4
    cn
    cB
    eldifi
    adantl
    #
    @20
    @12
    @127
    @5
    cO
    wph
    @12
    @127
    cO
    wf
    #
    @19
    isomenndlem.o
    adantr
    wph
    cn
    @12
    @4
    cA
    @36
    ffvelrnda
    ffvelrnd
    #
    syl2anc
    wph
    @16
    @19
    @128
    @108
    @132
    syldan
    #
    sge0splitmpt
    wph
    cc0
    @116
    cxad
    co
    @116
    @117
    @3
    wph
    @116
    wph
    @115
    cvv
    cB
    @123
    wph
    vn
    cB
    @8
    @127
    @115
    @133
    @115
    eqid
    fmptd
    sge0xrcl
    xaddid2d
    wph
    @114
    cc0
    @116
    cxad
    wph
    @114
    vn
    @110
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    wph
    @113
    @134
    csumge0
    wph
    vn
    @110
    @8
    cc0
    @126
    @8
    c0
    cO
    cfv
    #
    cc0
    @126
    @5
    c0
    cO
    @126
    @5
    @18
    c0
    @126
    @19
    @78
    @100
    @130
    @78
    @126
    @79
    a1i
    @102
    syl2anc
    @126
    @16
    @17
    c0
    @125
    @29
    wph
    @4
    cn
    cB
    eldifn
    adantl
    iffalsed
    eqtrd
    fveq2d
    @126
    wph
    @135
    cc0
    wceq
    @129
    isomenndlem.o0
    syl
    eqtrd
    mpteq2dva
    fveq2d
    wph
    @110
    vn
    cvv
    @119
    @122
    sge0z
    eqtrd
    oveq1d
    wph
    @3
    vy
    cY
    @56
    cO
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    @116
    @116
    wph
    @2
    @137
    csumge0
    wph
    vy
    @12
    @127
    cY
    cO
    isomenndlem.o
    isomenndlem.y
    feqresmpt
    fveq2d
    wph
    cY
    @136
    cB
    @8
    vy
    vn
    cF
    @5
    cvv
    wph
    vy
    nfv
    @119
    @56
    @5
    cO
    fveq2
    @123
    isomenndlem.f
    @22
    @5
    @17
    @109
    eqcomd
    @69
    @12
    @127
    @56
    cO
    wph
    @131
    @66
    isomenndlem.o
    adantr
    wph
    cY
    @12
    @56
    isomenndlem.y
    sselda
    ffvelrnd
    sge0f1o
    wph
    @116
    eqidd
    3eqtrd
    3eqtr4d
    3eqtrrd
    breq12d
    mpbird
end
