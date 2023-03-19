include "ccnfld.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cdiv.mm"
include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "wss.mm"
include "cc0.mm"
include "clt.mm"
include "wfn.mm"
include "wceq.mm"
include "cpnf.mm"
include "cico.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "fnresdm.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "ssid.mm"
include "jctil.mm"
include "cfn.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "sseq1.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "cnfld0.mm"
include "gsum0.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "oveq12d.mm"
include "rabbidv.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "0re.mm"
include "ltnri.mm"
include "pm2.21i.mm"
include "adantl.mm"
include "a1i.mm"
include "wel.mm"
include "wn.mm"
include "impexp.mm"
include "simprl.mm"
include "unssad.mm"
include "simpr.mm"
include "cr.mm"
include "ad3antrrr.mm"
include "cicc.mm"
include "simplll.mm"
include "sylan.mm"
include "c1.mm"
include "w3a.mm"
include "cmin.mm"
include "caddc.mm"
include "simpllr.mm"
include "adantr.mm"
include "eqid.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "ad2antrr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "csubmnd.mm"
include "rege0subm.mm"
include "fssresd.mm"
include "cvv.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "gsumsubmcl.mm"
include "elrege0.mm"
include "simplbi.mm"
include "elrpd.mm"
include "simprr.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "jensenlem2.mm"
include "sylibr.mm"
include "expr.mm"
include "embantd.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "remulcl.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"
include "fssd.mm"
include "inidm.mm"
include "off.mm"
include "ax-resscn.mm"
include "csupp.mm"
include "fex.mm"
include "offres.mm"
include "oveq1d.mm"
include "sstri.mm"
include "cdif.mm"
include "eldifi.mm"
include "fvres.mm"
include "difun2.mm"
include "difss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "csu.mm"
include "wral.mm"
include "cmpt.mm"
include "feqresmpt.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "sseldi.mm"
include "gsumfsum.mm"
include "3eqtrrd.mm"
include "fsum00.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "suppss.mm"
include "mul02.mm"
include "syl6ss.mm"
include "suppssof1.mm"
include "eqsstrd.mm"
include "gsumpt.mm"
include "sseldd.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "3eqtrd.mm"
include "ffvelrnd.mm"
include "simplrr.mm"
include "breqtrd.mm"
include "gt0ne0d.mm"
include "divcan3d.mm"
include "eqeltrd.mm"
include "leidd.mm"
include "fveq2d.mm"
include "fco.mm"
include "fnfco.mm"
include "fvco3.mm"
include "recnd.mm"
include "3brtr4d.mm"
include "sylanbrc.mm"
include "a1d.mm"
include "wo.mm"
include "simprbi.mm"
include "wb.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpjaodan.mm"
include "syl5bi.mm"
include "ex.mm"
include "com23.mm"
include "expcom.mm"
include "a2d.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpd.mm"
include "offn.mm"
include "3eltr3d.mm"

theorem jensen
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cT: class T
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cL: class L
  let cS: class S
  assume jensen.1: |- ( ph -> D C_ RR )
  assume jensen.2: |- ( ph -> F : D --> RR )
  assume jensen.3: |- ( ( ph /\ ( a e. D /\ b e. D ) ) -> ( a [,] b ) C_ D )
  assume jensen.4: |- ( ph -> A e. Fin )
  assume jensen.5: |- ( ph -> T : A --> ( 0 [,) +oo ) )
  assume jensen.6: |- ( ph -> X : A --> D )
  assume jensen.7: |- ( ph -> 0 < ( CCfld gsum T ) )
  assume jensen.8: |- ( ( ph /\ ( x e. D /\ y e. D /\ t e. ( 0 [,] 1 ) ) ) -> ( F ` ( ( t x. x ) + ( ( 1 - t ) x. y ) ) ) <_ ( ( t x. ( F ` x ) ) + ( ( 1 - t ) x. ( F ` y ) ) ) )

  disjoint a b
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint a ph
  disjoint b ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint T a
  disjoint T b
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint X a
  disjoint X b
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint a c
  disjoint a k
  disjoint a w
  disjoint b c
  disjoint b k
  disjoint b w
  disjoint c k
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint t w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint D c
  disjoint D k
  disjoint D w
  disjoint c ph
  disjoint k ph
  disjoint ph w
  disjoint F c
  disjoint F k
  disjoint F w
  disjoint T c
  disjoint T k
  disjoint T w
  disjoint X c
  disjoint X k
  disjoint X w
  disjoint a z
  disjoint B a
  disjoint b z
  disjoint B b
  disjoint t z
  disjoint B t
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint S a
  disjoint S b
  disjoint S t
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( ( ( CCfld gsum ( T oF x. X ) ) / ( CCfld gsum T ) ) e. D /\ ( F ` ( ( CCfld gsum ( T oF x. X ) ) / ( CCfld gsum T ) ) ) <_ ( ( CCfld gsum ( T oF x. ( F o. X ) ) ) / ( CCfld gsum T ) ) ) )

  proof
    wph
    ccnfld
    cT
    cX
    cmul
    cof
    #
    co
    #
    cgsu
    co
    #
    ccnfld
    cT
    cgsu
    co
    #
    cdiv
    co
    #
    vw
    cv
    #
    cF
    cfv
    #
    ccnfld
    cT
    cF
    cX
    ccom
    #
    @0
    co
    #
    cgsu
    co
    #
    @3
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    wcel
    @4
    cD
    wcel
    @4
    cF
    cfv
    #
    @10
    cle
    wbr
    #
    wa
    wph
    ccnfld
    @1
    cA
    cres
    #
    cgsu
    co
    #
    ccnfld
    cT
    cA
    cres
    #
    cgsu
    co
    #
    cdiv
    co
    #
    @6
    ccnfld
    @8
    cA
    cres
    #
    cgsu
    co
    #
    @18
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    @4
    @12
    wph
    cA
    cA
    wss
    #
    cc0
    @18
    clt
    wbr
    #
    wa
    #
    @19
    @24
    wcel
    #
    wph
    @26
    @25
    wph
    cc0
    @3
    @18
    clt
    jensen.7
    wph
    @17
    cT
    ccnfld
    cgsu
    wph
    cT
    cA
    wfn
    #
    @17
    cT
    wceq
    wph
    cA
    cc0
    cpnf
    cico
    co
    #
    cT
    wf
    #
    @29
    jensen.5
    cA
    @30
    cT
    ffn
    #
    syl
    #
    cA
    cT
    fnresdm
    syl
    oveq2d
    #
    breqtrrd
    cA
    ssid
    jctil
    cA
    cfn
    wcel
    #
    wph
    @27
    @28
    wi
    #
    jensen.4
    wph
    va
    cv
    #
    cA
    wss
    #
    cc0
    ccnfld
    cT
    @37
    cres
    #
    cgsu
    co
    #
    clt
    wbr
    #
    wa
    #
    ccnfld
    @1
    @37
    cres
    #
    cgsu
    co
    #
    @40
    cdiv
    co
    #
    @6
    ccnfld
    @8
    @37
    cres
    #
    cgsu
    co
    #
    @40
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    wcel
    #
    wi
    #
    wi
    wph
    c0
    cA
    wss
    #
    cc0
    cc0
    clt
    wbr
    #
    wa
    #
    ccnfld
    @1
    c0
    cres
    #
    cgsu
    co
    #
    cc0
    cdiv
    co
    #
    @6
    ccnfld
    @8
    c0
    cres
    #
    cgsu
    co
    #
    cc0
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    wcel
    #
    wi
    #
    wi
    wph
    vk
    cv
    #
    cA
    wss
    #
    cc0
    ccnfld
    cT
    @66
    cres
    #
    cgsu
    co
    #
    clt
    wbr
    #
    wa
    #
    ccnfld
    @1
    @66
    cres
    #
    cgsu
    co
    #
    @69
    cdiv
    co
    #
    @6
    ccnfld
    @8
    @66
    cres
    #
    cgsu
    co
    #
    @69
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    wcel
    #
    wi
    #
    wi
    wph
    @66
    vc
    cv
    #
    csn
    #
    cun
    #
    cA
    wss
    #
    cc0
    ccnfld
    cT
    @84
    cres
    #
    cgsu
    co
    #
    clt
    wbr
    #
    wa
    #
    ccnfld
    @1
    @84
    cres
    #
    cgsu
    co
    #
    @87
    cdiv
    co
    #
    @6
    ccnfld
    @8
    @84
    cres
    #
    cgsu
    co
    #
    @87
    cdiv
    co
    #
    cle
    wbr
    #
    vw
    cD
    crab
    #
    wcel
    #
    wi
    #
    wi
    wph
    @36
    wi
    va
    vk
    vc
    cA
    @37
    c0
    wceq
    #
    @52
    @65
    wph
    @100
    @42
    @55
    @51
    @64
    @100
    @38
    @53
    @41
    @54
    @37
    c0
    cA
    sseq1
    @100
    @40
    cc0
    cc0
    clt
    @100
    @40
    ccnfld
    c0
    cgsu
    co
    cc0
    @100
    @39
    c0
    ccnfld
    cgsu
    @100
    @39
    cT
    c0
    cres
    c0
    @37
    c0
    cT
    reseq2
    cT
    res0
    syl6eq
    oveq2d
    ccnfld
    cc0
    cnfld0
    gsum0
    syl6eq
    #
    breq2d
    anbi12d
    @100
    @45
    @58
    @50
    @63
    @100
    @44
    @57
    @40
    cc0
    cdiv
    @100
    @43
    @56
    ccnfld
    cgsu
    @37
    c0
    @1
    reseq2
    oveq2d
    @101
    oveq12d
    @100
    @49
    @62
    vw
    cD
    @100
    @48
    @61
    @6
    cle
    @100
    @47
    @60
    @40
    cc0
    cdiv
    @100
    @46
    @59
    ccnfld
    cgsu
    @37
    c0
    @8
    reseq2
    oveq2d
    @101
    oveq12d
    breq2d
    rabbidv
    eleq12d
    imbi12d
    imbi2d
    @37
    @66
    wceq
    #
    @52
    @81
    wph
    @102
    @42
    @71
    @51
    @80
    @102
    @38
    @67
    @41
    @70
    @37
    @66
    cA
    sseq1
    @102
    @40
    @69
    cc0
    clt
    @102
    @39
    @68
    ccnfld
    cgsu
    @37
    @66
    cT
    reseq2
    oveq2d
    #
    breq2d
    anbi12d
    @102
    @45
    @74
    @50
    @79
    @102
    @44
    @73
    @40
    @69
    cdiv
    @102
    @43
    @72
    ccnfld
    cgsu
    @37
    @66
    @1
    reseq2
    oveq2d
    @103
    oveq12d
    @102
    @49
    @78
    vw
    cD
    @102
    @48
    @77
    @6
    cle
    @102
    @47
    @76
    @40
    @69
    cdiv
    @102
    @46
    @75
    ccnfld
    cgsu
    @37
    @66
    @8
    reseq2
    oveq2d
    @103
    oveq12d
    breq2d
    rabbidv
    eleq12d
    imbi12d
    imbi2d
    @37
    @84
    wceq
    #
    @52
    @99
    wph
    @104
    @42
    @89
    @51
    @98
    @104
    @38
    @85
    @41
    @88
    @37
    @84
    cA
    sseq1
    @104
    @40
    @87
    cc0
    clt
    @104
    @39
    @86
    ccnfld
    cgsu
    @37
    @84
    cT
    reseq2
    oveq2d
    #
    breq2d
    anbi12d
    @104
    @45
    @92
    @50
    @97
    @104
    @44
    @91
    @40
    @87
    cdiv
    @104
    @43
    @90
    ccnfld
    cgsu
    @37
    @84
    @1
    reseq2
    oveq2d
    @105
    oveq12d
    @104
    @49
    @96
    vw
    cD
    @104
    @48
    @95
    @6
    cle
    @104
    @47
    @94
    @40
    @87
    cdiv
    @104
    @46
    @93
    ccnfld
    cgsu
    @37
    @84
    @8
    reseq2
    oveq2d
    @105
    oveq12d
    breq2d
    rabbidv
    eleq12d
    imbi12d
    imbi2d
    @37
    cA
    wceq
    #
    @52
    @36
    wph
    @106
    @42
    @27
    @51
    @28
    @106
    @38
    @25
    @41
    @26
    @37
    cA
    cA
    sseq1
    @106
    @40
    @18
    cc0
    clt
    @106
    @39
    @17
    ccnfld
    cgsu
    @37
    cA
    cT
    reseq2
    oveq2d
    #
    breq2d
    anbi12d
    @106
    @45
    @19
    @50
    @24
    @106
    @44
    @16
    @40
    @18
    cdiv
    @106
    @43
    @15
    ccnfld
    cgsu
    @37
    cA
    @1
    reseq2
    oveq2d
    @107
    oveq12d
    @106
    @49
    @23
    vw
    cD
    @106
    @48
    @22
    @6
    cle
    @106
    @47
    @21
    @40
    @18
    cdiv
    @106
    @46
    @20
    ccnfld
    cgsu
    @37
    cA
    @8
    reseq2
    oveq2d
    @107
    oveq12d
    breq2d
    rabbidv
    eleq12d
    imbi12d
    imbi2d
    @65
    wph
    @54
    @64
    @53
    @54
    @64
    cc0
    0re
    ltnri
    pm2.21i
    adantl
    a1i
    @66
    cfn
    wcel
    #
    vc
    vk
    wel
    wn
    #
    wa
    wph
    @81
    @99
    @109
    wph
    @81
    @99
    wi
    #
    wi
    @108
    wph
    @109
    @110
    wph
    @109
    wa
    #
    @89
    @81
    @98
    @111
    @89
    @81
    @98
    wi
    @81
    @67
    @70
    @80
    wi
    #
    wi
    @111
    @89
    wa
    #
    @98
    @67
    @70
    @80
    impexp
    @113
    @67
    @112
    @98
    @113
    @66
    @83
    cA
    @111
    @85
    @88
    simprl
    #
    unssad
    #
    @113
    @70
    @112
    @98
    wi
    cc0
    @69
    wceq
    #
    @113
    @70
    wa
    @70
    @80
    @98
    @113
    @70
    simpr
    @113
    @70
    @80
    @98
    @113
    @70
    @80
    wa
    #
    wa
    #
    @92
    cD
    wcel
    #
    @92
    cF
    cfv
    #
    @95
    cle
    wbr
    #
    wa
    @98
    @118
    vx
    vy
    vc
    vt
    cA
    @66
    cD
    @69
    cT
    cF
    @87
    cX
    va
    vb
    wph
    cD
    cr
    wss
    #
    @109
    @89
    @117
    jensen.1
    ad3antrrr
    wph
    cD
    cr
    cF
    wf
    #
    @109
    @89
    @117
    jensen.2
    ad3antrrr
    @118
    wph
    @37
    cD
    wcel
    vb
    cv
    #
    cD
    wcel
    wa
    @37
    @124
    cicc
    co
    cD
    wss
    wph
    @109
    @89
    @117
    simplll
    #
    jensen.3
    sylan
    @118
    wph
    @35
    @125
    jensen.4
    syl
    @118
    wph
    @31
    @125
    jensen.5
    syl
    @118
    wph
    cA
    cD
    cX
    wf
    #
    @125
    jensen.6
    syl
    wph
    cc0
    @3
    clt
    wbr
    @109
    @89
    @117
    jensen.7
    ad3antrrr
    @118
    wph
    vx
    cv
    #
    cD
    wcel
    vy
    cv
    #
    cD
    wcel
    vt
    cv
    #
    cc0
    c1
    cicc
    co
    wcel
    w3a
    @129
    @127
    cmul
    co
    c1
    @129
    cmin
    co
    #
    @128
    cmul
    co
    caddc
    co
    cF
    cfv
    @129
    @127
    cF
    cfv
    cmul
    co
    @130
    @128
    cF
    cfv
    cmul
    co
    caddc
    co
    cle
    wbr
    @125
    jensen.8
    sylan
    wph
    @109
    @89
    @117
    simpllr
    @113
    @85
    @117
    @114
    adantr
    @69
    eqid
    @87
    eqid
    @118
    @69
    @113
    @69
    cr
    wcel
    #
    @117
    @113
    @69
    @30
    wcel
    #
    @131
    @113
    @66
    @30
    @68
    ccnfld
    cfn
    cc0
    cnfld0
    ccnfld
    crg
    wcel
    #
    ccnfld
    ccmn
    wcel
    @113
    cnring
    ccnfld
    ringcmn
    mp1i
    @113
    @35
    @67
    @108
    wph
    @35
    @109
    @89
    jensen.4
    ad2antrr
    #
    @115
    cA
    @66
    ssfi
    syl2anc
    #
    @30
    ccnfld
    csubmnd
    cfv
    wcel
    @113
    rege0subm
    a1i
    @113
    cA
    @30
    @66
    cT
    wph
    @31
    @109
    @89
    jensen.5
    ad2antrr
    @115
    fssresd
    #
    @113
    @66
    @30
    @68
    cvv
    cc0
    @136
    @135
    cc0
    cvv
    wcel
    #
    @113
    c0ex
    a1i
    fdmfifsupp
    gsumsubmcl
    #
    @132
    @131
    cc0
    @69
    cle
    wbr
    #
    @69
    elrege0
    #
    simplbi
    syl
    #
    adantr
    @113
    @70
    @80
    simprl
    elrpd
    @118
    @74
    cD
    wcel
    #
    @74
    cF
    cfv
    #
    @77
    cle
    wbr
    #
    @118
    @80
    @142
    @144
    wa
    @113
    @70
    @80
    simprr
    @78
    @144
    vw
    @74
    cD
    @5
    @74
    wceq
    @6
    @143
    @77
    cle
    @5
    @74
    cF
    fveq2
    breq1d
    elrab
    sylib
    #
    simpld
    @118
    @142
    @144
    @145
    simprd
    jensenlem2
    @96
    @121
    vw
    @92
    cD
    @5
    @92
    wceq
    @6
    @120
    @95
    cle
    @5
    @92
    cF
    fveq2
    breq1d
    elrab
    #
    sylibr
    expr
    embantd
    @113
    @116
    wa
    #
    @98
    @112
    @147
    @119
    @121
    @98
    @147
    @92
    @82
    cX
    cfv
    #
    cD
    @147
    @92
    @82
    cT
    cfv
    #
    @148
    cmul
    co
    #
    @149
    cdiv
    co
    @148
    @147
    @91
    @150
    @87
    @149
    cdiv
    @147
    @91
    @82
    @90
    cfv
    #
    @82
    @1
    cfv
    #
    @150
    @147
    @84
    cc
    @90
    ccnfld
    cfn
    @82
    cc0
    cnfldbas
    cnfld0
    @133
    ccnfld
    cmnd
    wcel
    @147
    cnring
    ccnfld
    ringmnd
    mp1i
    #
    @113
    @84
    cfn
    wcel
    #
    @116
    @113
    @35
    @85
    @154
    @134
    @114
    cA
    @84
    ssfi
    syl2anc
    adantr
    #
    @82
    @84
    wcel
    #
    @147
    @83
    @84
    @82
    @83
    @66
    ssun2
    vc
    vsnid
    sselii
    a1i
    #
    @147
    cA
    cc
    @84
    @1
    wph
    cA
    cc
    @1
    wf
    #
    @109
    @89
    @116
    wph
    cA
    cr
    @1
    wf
    #
    cr
    cc
    wss
    #
    @158
    wph
    vx
    vy
    cA
    cA
    cA
    cmul
    cr
    cr
    cr
    cT
    cX
    cfn
    cfn
    @127
    cr
    wcel
    @128
    cr
    wcel
    wa
    @127
    @128
    cmul
    co
    cr
    wcel
    wph
    @127
    @128
    remulcl
    adantl
    #
    wph
    @31
    @30
    cr
    wss
    cA
    cr
    cT
    wf
    jensen.5
    rge0ssre
    cA
    @30
    cr
    cT
    fss
    sylancl
    #
    wph
    cA
    cD
    cr
    cX
    jensen.6
    jensen.1
    fssd
    jensen.4
    jensen.4
    cA
    inidm
    #
    off
    #
    ax-resscn
    cA
    cr
    cc
    @1
    fss
    sylancl
    ad3antrrr
    @113
    @85
    @116
    @114
    adantr
    #
    fssresd
    @147
    @90
    cc0
    csupp
    co
    @86
    cX
    @84
    cres
    #
    @0
    co
    #
    cc0
    csupp
    co
    @83
    @147
    @90
    @167
    cc0
    csupp
    @147
    cT
    cvv
    wcel
    #
    cX
    cvv
    wcel
    #
    @90
    @167
    wceq
    @147
    @31
    @35
    @168
    wph
    @31
    @109
    @89
    @116
    jensen.5
    ad3antrrr
    #
    @113
    @35
    @116
    @134
    adantr
    #
    cA
    @30
    cfn
    cT
    fex
    syl2anc
    #
    @147
    @126
    @35
    @169
    wph
    @126
    @109
    @89
    @116
    jensen.6
    ad3antrrr
    #
    @171
    cA
    cD
    cfn
    cX
    fex
    syl2anc
    @84
    cmul
    cT
    cX
    cvv
    cvv
    offres
    syl2anc
    oveq1d
    @147
    vx
    @86
    @166
    @84
    cc
    cvv
    @83
    cmul
    cc
    cfn
    cc0
    cc0
    @147
    @84
    cc
    vx
    @86
    @83
    cc0
    @147
    cA
    cc
    @84
    cT
    @147
    @31
    @30
    cc
    wss
    cA
    cc
    cT
    wf
    @170
    @30
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    cA
    @30
    cc
    cT
    fss
    sylancl
    #
    @165
    fssresd
    #
    @147
    @127
    @84
    @83
    cdif
    #
    wcel
    #
    wa
    #
    @127
    @86
    cfv
    #
    @127
    cT
    cfv
    #
    cc0
    @179
    @127
    @84
    wcel
    #
    @180
    @181
    wceq
    @178
    @182
    @147
    @127
    @84
    @83
    eldifi
    adantl
    @127
    @84
    cT
    fvres
    syl
    @178
    @147
    vx
    vk
    wel
    #
    @181
    cc0
    wceq
    #
    @177
    @66
    @127
    @177
    @66
    @83
    cdif
    @66
    @66
    @83
    difun2
    @66
    @83
    difss
    eqsstri
    sseli
    @147
    @184
    vx
    @66
    @147
    @66
    @181
    vx
    csu
    #
    cc0
    wceq
    @184
    vx
    @66
    wral
    @147
    cc0
    @69
    ccnfld
    vx
    @66
    @181
    cmpt
    #
    cgsu
    co
    @185
    @113
    @116
    simpr
    @147
    @68
    @186
    ccnfld
    cgsu
    @147
    vx
    cA
    @30
    @66
    cT
    @170
    @113
    @67
    @116
    @115
    adantr
    #
    feqresmpt
    oveq2d
    @147
    @66
    @181
    vx
    @113
    @108
    @116
    @135
    adantr
    #
    @147
    @183
    wa
    #
    @30
    cc
    @181
    @174
    @147
    @183
    @127
    cA
    wcel
    @181
    @30
    wcel
    #
    @147
    @66
    cA
    @127
    @187
    sselda
    @147
    cA
    @30
    @127
    cT
    @170
    ffvelrnda
    syldan
    #
    sseldi
    gsumfsum
    3eqtrrd
    @147
    @66
    @181
    vx
    @188
    @189
    @181
    cr
    wcel
    #
    cc0
    @181
    cle
    wbr
    #
    @189
    @190
    @192
    @193
    wa
    @191
    @181
    elrege0
    sylib
    #
    simpld
    @189
    @192
    @193
    @194
    simprd
    fsum00
    mpbid
    r19.21bi
    sylan2
    eqtrd
    suppss
    #
    @127
    cc
    wcel
    cc0
    @127
    cmul
    co
    cc0
    wceq
    @147
    @127
    mul02
    adantl
    #
    @176
    @147
    cA
    cc
    @84
    cX
    @147
    cA
    cD
    cc
    cX
    @173
    @147
    cD
    cr
    cc
    wph
    @122
    @109
    @89
    @116
    jensen.1
    ad3antrrr
    ax-resscn
    syl6ss
    fssd
    #
    @165
    fssresd
    @155
    @137
    @147
    c0ex
    a1i
    #
    suppssof1
    eqsstrd
    gsumpt
    @147
    @156
    @151
    @152
    wceq
    @157
    @82
    @84
    @1
    fvres
    syl
    @147
    @29
    cX
    cA
    wfn
    #
    @35
    @82
    cA
    wcel
    #
    @152
    @150
    wceq
    @147
    @31
    @29
    @170
    @32
    syl
    #
    @147
    @126
    @199
    @173
    cA
    cD
    cX
    ffn
    syl
    @171
    @147
    @84
    cA
    @82
    @165
    @157
    sseldd
    #
    cA
    cmul
    cT
    cX
    cfn
    @82
    fnfvof
    syl22anc
    3eqtrd
    @147
    @87
    @82
    @86
    cfv
    #
    @149
    @147
    @84
    cc
    @86
    ccnfld
    cfn
    @82
    cc0
    cnfldbas
    cnfld0
    @153
    @155
    @157
    @176
    @195
    gsumpt
    @147
    @156
    @203
    @149
    wceq
    @157
    @82
    @84
    cT
    fvres
    syl
    eqtrd
    #
    oveq12d
    @147
    @148
    @149
    @147
    cA
    cc
    @82
    cX
    @197
    @202
    ffvelrnd
    @147
    cA
    cc
    @82
    cT
    @175
    @202
    ffvelrnd
    #
    @147
    @149
    @147
    cc0
    @87
    @149
    clt
    @111
    @85
    @88
    @116
    simplrr
    @204
    breqtrd
    gt0ne0d
    #
    divcan3d
    eqtrd
    #
    @147
    cA
    cD
    @82
    cX
    @173
    @202
    ffvelrnd
    #
    eqeltrd
    @147
    @148
    cF
    cfv
    #
    @209
    @120
    @95
    cle
    @147
    @209
    @147
    cD
    cr
    @148
    cF
    wph
    @123
    @109
    @89
    @116
    jensen.2
    ad3antrrr
    @208
    ffvelrnd
    #
    leidd
    @147
    @92
    @148
    cF
    @207
    fveq2d
    @147
    @95
    @149
    @209
    cmul
    co
    #
    @149
    cdiv
    co
    @209
    @147
    @94
    @211
    @87
    @149
    cdiv
    @147
    @94
    @82
    @93
    cfv
    #
    @82
    @8
    cfv
    #
    @211
    @147
    @84
    cc
    @93
    ccnfld
    cfn
    @82
    cc0
    cnfldbas
    cnfld0
    @153
    @155
    @157
    @147
    cA
    cc
    @84
    @8
    wph
    cA
    cc
    @8
    wf
    #
    @109
    @89
    @116
    wph
    cA
    cr
    @8
    wf
    @160
    @214
    wph
    vx
    vy
    cA
    cA
    cA
    cmul
    cr
    cr
    cr
    cT
    @7
    cfn
    cfn
    @161
    @162
    wph
    @123
    @126
    cA
    cr
    @7
    wf
    #
    jensen.2
    jensen.6
    cA
    cD
    cr
    cF
    cX
    fco
    syl2anc
    #
    jensen.4
    jensen.4
    @163
    off
    ax-resscn
    cA
    cr
    cc
    @8
    fss
    sylancl
    ad3antrrr
    @165
    fssresd
    @147
    @93
    cc0
    csupp
    co
    @86
    @7
    @84
    cres
    #
    @0
    co
    #
    cc0
    csupp
    co
    @83
    @147
    @93
    @218
    cc0
    csupp
    @147
    @168
    @7
    cvv
    wcel
    #
    @93
    @218
    wceq
    @172
    @147
    @215
    @35
    @219
    wph
    @215
    @109
    @89
    @116
    @216
    ad3antrrr
    #
    @171
    cA
    cr
    cfn
    @7
    fex
    syl2anc
    @84
    cmul
    cT
    @7
    cvv
    cvv
    offres
    syl2anc
    oveq1d
    @147
    vx
    @86
    @217
    @84
    cc
    cvv
    @83
    cmul
    cc
    cfn
    cc0
    cc0
    @195
    @196
    @176
    @147
    cA
    cc
    @84
    @7
    @147
    @215
    @160
    cA
    cc
    @7
    wf
    @220
    ax-resscn
    cA
    cr
    cc
    @7
    fss
    sylancl
    @165
    fssresd
    @155
    @198
    suppssof1
    eqsstrd
    gsumpt
    @147
    @156
    @212
    @213
    wceq
    @157
    @82
    @84
    @8
    fvres
    syl
    @147
    @213
    @149
    @82
    @7
    cfv
    #
    cmul
    co
    #
    @211
    @147
    @29
    @7
    cA
    wfn
    #
    @35
    @200
    @213
    @222
    wceq
    @201
    wph
    @223
    @109
    @89
    @116
    wph
    cF
    cD
    wfn
    #
    @126
    @223
    wph
    @123
    @224
    jensen.2
    cD
    cr
    cF
    ffn
    syl
    jensen.6
    cD
    cA
    cF
    cX
    fnfco
    syl2anc
    #
    ad3antrrr
    @171
    @202
    cA
    cmul
    cT
    @7
    cfn
    @82
    fnfvof
    syl22anc
    @147
    @221
    @209
    @149
    cmul
    @147
    @126
    @200
    @221
    @209
    wceq
    @173
    @202
    cA
    cD
    @82
    cF
    cX
    fvco3
    syl2anc
    oveq2d
    eqtrd
    3eqtrd
    @204
    oveq12d
    @147
    @209
    @149
    @147
    @209
    @210
    recnd
    @205
    @206
    divcan3d
    eqtrd
    3brtr4d
    @146
    sylanbrc
    a1d
    @113
    @139
    @70
    @116
    wo
    #
    @113
    @132
    @139
    @138
    @132
    @131
    @139
    @140
    simprbi
    syl
    @113
    cc0
    cr
    wcel
    @131
    @139
    @226
    wb
    0re
    @141
    cc0
    @69
    leloe
    sylancr
    mpbid
    mpjaodan
    embantd
    syl5bi
    ex
    com23
    expcom
    adantl
    a2d
    findcard2s
    mpcom
    mpd
    wph
    @16
    @2
    @18
    @3
    cdiv
    wph
    @15
    @1
    ccnfld
    cgsu
    wph
    @1
    cA
    wfn
    #
    @15
    @1
    wceq
    wph
    @159
    @227
    @164
    cA
    cr
    @1
    ffn
    syl
    cA
    @1
    fnresdm
    syl
    oveq2d
    @34
    oveq12d
    wph
    @23
    @11
    vw
    cD
    wph
    @22
    @10
    @6
    cle
    wph
    @21
    @9
    @18
    @3
    cdiv
    wph
    @20
    @8
    ccnfld
    cgsu
    wph
    @8
    cA
    wfn
    @20
    @8
    wceq
    wph
    cA
    cA
    cmul
    cA
    cT
    @7
    cfn
    cfn
    @33
    @225
    jensen.4
    jensen.4
    @163
    offn
    cA
    @8
    fnresdm
    syl
    oveq2d
    @34
    oveq12d
    breq2d
    rabbidv
    3eltr3d
    @11
    @14
    vw
    @4
    cD
    @5
    @4
    wceq
    @6
    @13
    @10
    cle
    @5
    @4
    cF
    fveq2
    breq1d
    elrab
    sylib
end
