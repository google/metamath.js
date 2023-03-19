include "caddc.mm"
include "co.mm"
include "cicc.mm"
include "cv.mm"
include "cfv.mm"
include "citg.mm"
include "cdit.mm"
include "c1.mm"
include "cmul.mm"
include "cioo.mm"
include "rpred.mm"
include "leadd1dd.mm"
include "ditgpos.mm"
include "readdcld.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "itgioo.mm"
include "eqtr2d.mm"
include "cmpt.mm"
include "eqid.mm"
include "ccncf.mm"
include "recnd.mm"
include "addccncf.mm"
include "syl.mm"
include "iccssred.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simp3d.mm"
include "eliccd.mm"
include "cncfmptssg.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "cres.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "cdm.mm"
include "wss.mm"
include "ffdm.mm"
include "simpld.mm"
include "wi.mm"
include "wral.mm"
include "simp3.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "ralrimivw.mm"
include "rabss.mm"
include "sylibr.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "cncfperiod.mm"
include "elrab.mm"
include "simprr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "sylan2b.mm"
include "cmin.mm"
include "resubcld.mm"
include "pncand.mm"
include "eqcomd.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "breqtrd.mm"
include "npcand.mm"
include "rspcev.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "eqrdv.mm"
include "reseq2d.mm"
include "eqsstr3d.mm"
include "feqresmpt.mm"
include "iccshift.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "cibl.mm"
include "ioosscn.mm"
include "a1i.mm"
include "1cnd.mm"
include "ssid.mm"
include "constcncfg.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "cvol.mm"
include "ioombl.mm"
include "ioovolcl.mm"
include "iblconst.mm"
include "syl5eqelr.mm"
include "elind.mm"
include "cdv.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "resmptd.mm"
include "oveq2d.mm"
include "addcld.mm"
include "fmptd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "eqtrd.mm"
include "iccntr.mm"
include "cc0.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "dvmptid.mm"
include "0cnd.mm"
include "dvmptc.mm"
include "dvmptadd.mm"
include "reseq1d.mm"
include "ioossre.mm"
include "1p0e1.mm"
include "mpteq2i.mm"
include "3eqtrd.mm"
include "fveq2.mm"
include "itgsubsticc.mm"
include "mulcld.mm"
include "fveq2d.mm"
include "cbvitgv.mm"
include "mulid1d.mm"
include "itgeq2dv.mm"
include "syl5eq.mm"

theorem itgperiod
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume itgperiod.a: |- ( ph -> A e. RR )
  assume itgperiod.b: |- ( ph -> B e. RR )
  assume itgperiod.aleb: |- ( ph -> A <_ B )
  assume itgperiod.t: |- ( ph -> T e. RR+ )
  assume itgperiod.f: |- ( ph -> F : RR --> CC )
  assume itgperiod.fper: |- ( ( ph /\ x e. ( A [,] B ) ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume itgperiod.fcn: |- ( ph -> ( F |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> CC ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint T x
  disjoint ph x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> S. ( ( A + T ) [,] ( B + T ) ) ( F ` x ) _d x = S. ( A [,] B ) ( F ` x ) _d x )

  proof
    wph
    vx
    cA
    cT
    caddc
    co
    #
    cB
    cT
    caddc
    co
    #
    cicc
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    citg
    #
    vx
    @0
    @1
    @4
    cdit
    #
    vy
    cA
    cB
    vy
    cv
    #
    cT
    caddc
    co
    #
    cF
    cfv
    #
    c1
    cmul
    co
    #
    cdit
    #
    vx
    cA
    cB
    cicc
    co
    #
    @4
    citg
    #
    wph
    @6
    vx
    @0
    @1
    cioo
    co
    @4
    citg
    @5
    wph
    vx
    @0
    @1
    @4
    wph
    cA
    cB
    cT
    itgperiod.a
    itgperiod.b
    wph
    cT
    itgperiod.t
    rpred
    #
    itgperiod.aleb
    leadd1dd
    ditgpos
    wph
    vx
    @0
    @1
    @4
    wph
    cA
    cT
    itgperiod.a
    @14
    readdcld
    #
    wph
    cB
    cT
    itgperiod.b
    @14
    readdcld
    #
    wph
    @3
    @2
    wcel
    #
    wa
    #
    cr
    cc
    @3
    cF
    wph
    cr
    cc
    cF
    wf
    #
    @17
    itgperiod.f
    adantr
    @18
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @17
    @3
    cr
    wcel
    #
    wph
    @20
    @17
    @15
    adantr
    #
    wph
    @21
    @17
    @16
    adantr
    #
    wph
    @17
    simpr
    #
    @0
    @1
    @3
    eliccre
    syl3anc
    #
    ffvelrnd
    itgioo
    eqtr2d
    wph
    vy
    vx
    @8
    c1
    @4
    @9
    @0
    @1
    cA
    cB
    itgperiod.a
    itgperiod.b
    itgperiod.aleb
    wph
    vy
    cc
    cc
    @12
    @2
    @8
    vy
    cc
    @8
    cmpt
    #
    @27
    eqid
    #
    wph
    cT
    cc
    wcel
    #
    @27
    cc
    cc
    ccncf
    co
    wcel
    wph
    cT
    @14
    recnd
    #
    vy
    cT
    @27
    @28
    addccncf
    syl
    wph
    @12
    cr
    cc
    wph
    cA
    cB
    itgperiod.a
    itgperiod.b
    iccssred
    #
    ax-resscn
    syl6ss
    #
    wph
    @2
    cr
    cc
    wph
    @0
    @1
    @15
    @16
    iccssred
    ax-resscn
    syl6ss
    wph
    @7
    @12
    wcel
    #
    wa
    #
    @0
    @1
    @8
    wph
    @20
    @33
    @15
    adantr
    wph
    @21
    @33
    @16
    adantr
    @34
    @7
    cT
    wph
    @12
    cr
    @7
    @31
    sselda
    #
    wph
    cT
    cr
    wcel
    #
    @33
    @14
    adantr
    #
    readdcld
    #
    @34
    cA
    @7
    cT
    wph
    cA
    cr
    wcel
    #
    @33
    itgperiod.a
    adantr
    #
    @35
    @37
    @34
    @7
    cr
    wcel
    #
    cA
    @7
    cle
    wbr
    #
    @7
    cB
    cle
    wbr
    #
    @34
    @33
    @41
    @42
    @43
    w3a
    #
    wph
    @33
    simpr
    @34
    @39
    cB
    cr
    wcel
    #
    @33
    @44
    wb
    @40
    wph
    @45
    @33
    itgperiod.b
    adantr
    #
    cA
    cB
    @7
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    leadd1dd
    @34
    @7
    cB
    cT
    @35
    @46
    @37
    @34
    @41
    @42
    @43
    @47
    simp3d
    leadd1dd
    eliccd
    cncfmptssg
    wph
    cF
    vw
    cv
    #
    vz
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vz
    @12
    wrex
    #
    vw
    cc
    crab
    #
    cres
    #
    @53
    cc
    ccncf
    co
    vx
    @2
    @4
    cmpt
    #
    @2
    cc
    ccncf
    co
    wph
    vx
    vy
    @12
    @53
    cT
    cF
    @32
    @14
    @52
    @3
    @8
    wceq
    #
    vy
    @12
    wrex
    #
    vw
    vx
    cc
    @48
    @3
    wceq
    #
    @52
    @3
    @50
    wceq
    #
    vz
    @12
    wrex
    #
    @57
    @58
    @51
    @59
    vz
    @12
    @48
    @3
    @50
    eqeq1
    rexbidv
    #
    @59
    @56
    vz
    vy
    @12
    @49
    @7
    wceq
    @50
    @8
    @3
    @49
    @7
    cT
    caddc
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvrabv
    wph
    cF
    cdm
    #
    cc
    cF
    wf
    #
    @62
    cr
    wss
    #
    wph
    @19
    @63
    @64
    wa
    itgperiod.f
    cr
    cc
    cF
    ffdm
    syl
    simpld
    #
    wph
    @53
    cr
    @62
    wph
    @52
    @48
    cr
    wcel
    #
    wi
    #
    vw
    cc
    wral
    @53
    cr
    wss
    wph
    @67
    vw
    cc
    wph
    @51
    @66
    vz
    @12
    wph
    @49
    @12
    wcel
    #
    @51
    w3a
    @48
    @50
    cr
    wph
    @68
    @51
    simp3
    wph
    @68
    @50
    cr
    wcel
    #
    @51
    wph
    @68
    wa
    #
    @49
    cT
    wph
    @12
    cr
    @49
    @31
    sselda
    #
    wph
    @36
    @68
    @14
    adantr
    #
    readdcld
    #
    3adant3
    eqeltrd
    rexlimdv3a
    ralrimivw
    @52
    vw
    cc
    cr
    rabss
    sylibr
    wph
    @19
    @62
    cr
    wceq
    itgperiod.f
    cr
    cc
    cF
    fdm
    syl
    sseqtr4d
    #
    itgperiod.fper
    itgperiod.fcn
    cncfperiod
    wph
    @54
    cF
    @2
    cres
    @55
    wph
    @53
    @2
    cF
    wph
    vx
    @53
    @2
    wph
    @3
    @53
    wcel
    #
    @17
    @75
    wph
    @3
    cc
    wcel
    #
    @60
    wa
    #
    @17
    @52
    @60
    vw
    @3
    cc
    @61
    elrab
    #
    wph
    @77
    wa
    #
    @60
    @17
    wph
    @76
    @60
    simprr
    @79
    @59
    @17
    vz
    @12
    wph
    @77
    vz
    wph
    vz
    nfv
    @76
    @60
    vz
    @76
    vz
    nfv
    @59
    vz
    @12
    nfre1
    nfan
    nfan
    @17
    vz
    nfv
    wph
    @68
    @59
    @17
    wi
    wi
    @77
    wph
    @68
    @59
    @17
    wph
    @68
    @59
    w3a
    #
    @3
    @50
    @2
    wph
    @68
    @59
    simp3
    @80
    @50
    @2
    wcel
    #
    @69
    @0
    @50
    cle
    wbr
    #
    @50
    @1
    cle
    wbr
    #
    w3a
    #
    wph
    @68
    @84
    @59
    @70
    @69
    @82
    @83
    @73
    @70
    cA
    @49
    cT
    wph
    @39
    @68
    itgperiod.a
    adantr
    #
    @71
    @72
    @70
    @49
    cr
    wcel
    #
    cA
    @49
    cle
    wbr
    #
    @49
    cB
    cle
    wbr
    #
    @70
    @68
    @86
    @87
    @88
    w3a
    #
    wph
    @68
    simpr
    @70
    @39
    @45
    @68
    @89
    wb
    @85
    wph
    @45
    @68
    itgperiod.b
    adantr
    #
    cA
    cB
    @49
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    leadd1dd
    @70
    @49
    cB
    cT
    @71
    @90
    @72
    @70
    @86
    @87
    @88
    @91
    simp3d
    leadd1dd
    3jca
    3adant3
    @80
    @20
    @21
    @81
    @84
    wb
    wph
    @68
    @20
    @59
    @15
    3ad2ant1
    wph
    @68
    @21
    @59
    @16
    3ad2ant1
    @0
    @1
    @50
    elicc2
    syl2anc
    mpbird
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    sylan2b
    @18
    @76
    @60
    @75
    @18
    @3
    @26
    recnd
    #
    @18
    @3
    cT
    cmin
    co
    #
    @12
    wcel
    @3
    @93
    cT
    caddc
    co
    #
    wceq
    #
    @60
    @18
    cA
    cB
    @93
    wph
    @39
    @17
    itgperiod.a
    adantr
    wph
    @45
    @17
    itgperiod.b
    adantr
    @18
    @3
    cT
    @26
    wph
    @36
    @17
    @14
    adantr
    #
    resubcld
    @18
    cA
    @0
    cT
    cmin
    co
    #
    @93
    cle
    wph
    cA
    @97
    wceq
    @17
    wph
    @97
    cA
    wph
    cA
    cT
    wph
    cA
    itgperiod.a
    recnd
    @30
    pncand
    eqcomd
    adantr
    @18
    @0
    @3
    cT
    @23
    @26
    @96
    @18
    @22
    @0
    @3
    cle
    wbr
    #
    @3
    @1
    cle
    wbr
    #
    @18
    @17
    @22
    @98
    @99
    w3a
    #
    @25
    @18
    @20
    @21
    @17
    @100
    wb
    @23
    @24
    @0
    @1
    @3
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    lesub1dd
    eqbrtrd
    @18
    @93
    @1
    cT
    cmin
    co
    #
    cB
    cle
    @18
    @3
    @1
    cT
    @26
    @24
    @96
    @18
    @22
    @98
    @99
    @101
    simp3d
    lesub1dd
    wph
    @102
    cB
    wceq
    @17
    wph
    cB
    cT
    wph
    cB
    itgperiod.b
    recnd
    @30
    pncand
    adantr
    breqtrd
    eliccd
    @18
    @94
    @3
    @18
    @3
    cT
    @92
    wph
    @29
    @17
    @30
    adantr
    npcand
    eqcomd
    @59
    @95
    vz
    @93
    @12
    @49
    @93
    wceq
    @50
    @94
    @3
    @49
    @93
    cT
    caddc
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @78
    sylanbrc
    impbida
    eqrdv
    #
    reseq2d
    wph
    vx
    @62
    cc
    @2
    cF
    @65
    wph
    @2
    @53
    @62
    @103
    @74
    eqsstr3d
    feqresmpt
    eqtr2d
    wph
    @2
    @53
    cc
    ccncf
    wph
    vz
    vw
    cA
    cB
    cT
    itgperiod.a
    itgperiod.b
    @14
    iccshift
    oveq1d
    3eltr4d
    wph
    cA
    cB
    cioo
    co
    #
    cc
    ccncf
    co
    cibl
    vy
    @104
    c1
    cmpt
    #
    wph
    vy
    @104
    c1
    cc
    @104
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    wph
    1cnd
    #
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    constcncfg
    wph
    @105
    @104
    c1
    csn
    cxp
    #
    cibl
    vy
    @104
    c1
    fconstmpt
    wph
    @104
    cvol
    cdm
    wcel
    #
    @104
    cvol
    cfv
    cr
    wcel
    #
    c1
    cc
    wcel
    @107
    cibl
    wcel
    @108
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @39
    @45
    @109
    itgperiod.a
    itgperiod.b
    cA
    cB
    ioovolcl
    syl2anc
    @106
    @104
    c1
    iblconst
    syl3anc
    syl5eqelr
    elind
    wph
    cr
    vy
    @12
    @8
    cmpt
    #
    cdv
    co
    #
    cr
    vy
    cr
    @8
    cmpt
    #
    cdv
    co
    #
    @12
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @113
    @104
    cres
    #
    @105
    wph
    @111
    cr
    @112
    @12
    cres
    #
    cdv
    co
    #
    @116
    wph
    @110
    @118
    cr
    cdv
    wph
    @118
    @110
    wph
    vy
    cr
    @12
    @8
    @31
    resmptd
    eqcomd
    oveq2d
    wph
    cr
    cc
    wss
    #
    cr
    cc
    @112
    wf
    cr
    cr
    wss
    #
    @12
    cr
    wss
    @119
    @116
    wceq
    @120
    wph
    ax-resscn
    a1i
    #
    wph
    vy
    cr
    @8
    cc
    @112
    wph
    @41
    wa
    #
    @7
    cT
    wph
    cr
    cc
    @7
    @122
    sselda
    #
    wph
    @29
    @41
    @30
    adantr
    #
    addcld
    @112
    eqid
    fmptd
    @121
    wph
    cr
    ssid
    a1i
    @31
    cr
    @12
    cr
    @114
    @112
    ccnfld
    ctopn
    cfv
    #
    @126
    eqid
    #
    @126
    @127
    tgioo2
    dvres
    syl22anc
    eqtrd
    wph
    @115
    @104
    @113
    wph
    @39
    @45
    @115
    @104
    wceq
    itgperiod.a
    itgperiod.b
    cA
    cB
    iccntr
    syl2anc
    reseq2d
    wph
    @117
    vy
    cr
    c1
    cc0
    caddc
    co
    #
    cmpt
    #
    @104
    cres
    vy
    @104
    @128
    cmpt
    #
    @105
    wph
    @113
    @129
    @104
    wph
    vy
    @7
    c1
    cT
    cc0
    cr
    cc
    cc
    cr
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    #
    @124
    @123
    1cnd
    wph
    vy
    cr
    @131
    dvmptid
    @125
    @123
    0cnd
    wph
    vy
    cT
    cr
    @131
    @30
    dvmptc
    dvmptadd
    reseq1d
    wph
    vy
    cr
    @104
    @128
    @104
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    resmptd
    @130
    @105
    wceq
    wph
    vy
    @104
    @128
    c1
    1p0e1
    mpteq2i
    a1i
    3eqtrd
    3eqtrd
    @3
    @8
    cF
    fveq2
    @7
    cA
    cT
    caddc
    oveq1
    @7
    cB
    cT
    caddc
    oveq1
    @15
    @16
    itgsubsticc
    wph
    @11
    vy
    @104
    @10
    citg
    vy
    @12
    @10
    citg
    #
    @13
    wph
    vy
    cA
    cB
    @10
    itgperiod.aleb
    ditgpos
    wph
    vy
    cA
    cB
    @10
    itgperiod.a
    itgperiod.b
    @34
    @9
    c1
    @34
    cr
    cc
    @8
    cF
    wph
    @19
    @33
    itgperiod.f
    adantr
    @38
    ffvelrnd
    @34
    1cnd
    mulcld
    itgioo
    wph
    @132
    vx
    @12
    @3
    cT
    caddc
    co
    #
    cF
    cfv
    #
    c1
    cmul
    co
    #
    citg
    @13
    vy
    vx
    @12
    @10
    @135
    @7
    @3
    wceq
    #
    @9
    @134
    c1
    cmul
    @136
    @8
    @133
    cF
    @7
    @3
    cT
    caddc
    oveq1
    fveq2d
    oveq1d
    cbvitgv
    wph
    vx
    @12
    @135
    @4
    wph
    @3
    @12
    wcel
    #
    wa
    #
    @135
    @134
    @4
    @138
    @134
    @138
    cr
    cc
    @133
    cF
    wph
    @19
    @137
    itgperiod.f
    adantr
    @138
    @3
    cT
    wph
    @12
    cr
    @3
    @31
    sselda
    wph
    @36
    @137
    @14
    adantr
    readdcld
    ffvelrnd
    mulid1d
    itgperiod.fper
    eqtrd
    itgeq2dv
    syl5eq
    3eqtrd
    3eqtrd
end
