include "cn.mm"
include "ciun.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cxne.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "wbr.mm"
include "iunin2.mm"
include "fveq2i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "cpw.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "elpwincl1.mm"
include "elpwiuncl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "syl5eqelr.mm"
include "elpwdifcl.mm"
include "xnegcld.mm"
include "xaddcld.mm"
include "cesum.mm"
include "wral.mm"
include "wf.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "dfiun3g.mm"
include "syl.mm"
include "fveq2d.mm"
include "com.mm"
include "cdom.mm"
include "wss.mm"
include "nnct.mm"
include "mptct.mm"
include "rnct.mm"
include "mp2b.mm"
include "eqid.mm"
include "rnmptss.mm"
include "w3a.mm"
include "wi.mm"
include "mptexg.mm"
include "rnexg.mm"
include "breq1.mm"
include "sseq1.mm"
include "3anbi23d.mm"
include "unieq.mm"
include "esumeq1.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ax-mp.mm"
include "mpd3an23.mm"
include "eqbrtrd.mm"
include "fveq2.mm"
include "c0.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "wdisj.mm"
include "disjin.mm"
include "wb.mm"
include "incom.mm"
include "rgenw.mm"
include "disjeq2.mm"
include "sylib.mm"
include "esumrnmpt2.mm"
include "breqtrd.mm"
include "difssd.mm"
include "carsgmon.mm"
include "xrge0subcld.mm"
include "c1.mm"
include "cfz.mm"
include "cmnf.mm"
include "wne.mm"
include "xrge0neqmnf.mm"
include "xnegneg.mm"
include "xnegeq.mm"
include "adantl.mm"
include "xnegmnf.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "ccarsg.mm"
include "simpll.mm"
include "fz1ssnn.mm"
include "sselda.mm"
include "3adant1r.mm"
include "cfn.mm"
include "fzfi.mm"
include "mptfi.mm"
include "rnfi.mm"
include "fiunelcarsg.mm"
include "eqeltrd.mm"
include "elcarsg.mm"
include "mpbid.mm"
include "simprd.mm"
include "ineq1.mm"
include "difeq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "xaddpnf1.mm"
include "3eqtr3d.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "xaddass.mm"
include "syl222anc.mm"
include "xnegid.mm"
include "xaddid1.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "ineq2d.mm"
include "mptss.mm"
include "rnss.mm"
include "disjrnmpt.mm"
include "disjss1.mm"
include "carsgclctunlem1.mm"
include "ineq2.mm"
include "elexi.mm"
include "inss2.mm"
include "sseq2.mm"
include "mpbii.mm"
include "ss0.mm"
include "3eqtr3rd.mm"
include "iunss1.mm"
include "mp1i.mm"
include "sscond.mm"
include "xleneg.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "xleadd2a.mm"
include "syl31anc.mm"
include "esumgect.mm"
include "xrletrd.mm"
include "syl5eqbrr.mm"
include "xleadd1a.mm"
include "xrge0npcan.mm"
include "syl3anc.mm"

theorem carsgclctunlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vk: setvar k
  let cE: class E
  let cM: class M
  let cO: class O
  let cV: class V
  let ve: setvar e
  let vn: setvar n
  let va: setvar a
  let vm: setvar m
  let vb: setvar b
  let vf: setvar f
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume carsgsiga.3: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )
  assume carsgclctunlem2.1: |- ( ph -> Disj_ k e. NN A )
  assume carsgclctunlem2.2: |- ( ( ph /\ k e. NN ) -> A e. ( toCaraSiga ` M ) )
  assume carsgclctunlem2.3: |- ( ph -> E e. ~P O )
  assume carsgclctunlem2.4: |- ( ph -> ( M ` E ) =/= +oo )

  disjoint k x
  disjoint k y
  disjoint x y
  disjoint E k
  disjoint M k
  disjoint O k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint E x
  disjoint E y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint e k
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint k n
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint E n
  disjoint M n
  disjoint n ph
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> ( ( M ` ( E i^i U_ k e. NN A ) ) +e ( M ` ( E \ U_ k e. NN A ) ) ) <_ ( M ` E ) )

  proof
    wph
    cE
    vk
    cn
    cA
    ciun
    #
    cin
    #
    cM
    cfv
    #
    cE
    @0
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    cE
    cM
    cfv
    #
    @4
    cxne
    #
    cxad
    co
    #
    @4
    cxad
    co
    #
    @6
    cle
    wph
    @2
    cxr
    wcel
    @8
    cxr
    wcel
    @4
    cxr
    wcel
    #
    @2
    @8
    cle
    wbr
    @5
    @9
    cle
    wbr
    wph
    @2
    vk
    cn
    cE
    cA
    cin
    #
    ciun
    #
    cM
    cfv
    #
    cxr
    @12
    @1
    cM
    vk
    cn
    cE
    cA
    iunin2
    fveq2i
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @13
    cc0
    cpnf
    iccssxr
    #
    wph
    cO
    cpw
    #
    @15
    @12
    cM
    carsgval.2
    wph
    cn
    @11
    cO
    vk
    cvv
    cn
    cvv
    wcel
    #
    wph
    nnex
    a1i
    #
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    #
    cE
    cA
    cO
    wph
    cE
    @17
    wcel
    #
    @21
    carsgclctunlem2.3
    adantr
    elpwincl1
    #
    elpwiuncl
    ffvelrnd
    sseldi
    #
    syl5eqelr
    wph
    @6
    @7
    wph
    @15
    cxr
    @6
    @16
    wph
    @17
    @15
    cE
    cM
    carsgval.2
    carsgclctunlem2.3
    ffvelrnd
    #
    sseldi
    #
    wph
    @4
    wph
    @15
    cxr
    @4
    @16
    wph
    @17
    @15
    @3
    cM
    carsgval.2
    wph
    cE
    @0
    cO
    carsgclctunlem2.3
    elpwdifcl
    ffvelrnd
    #
    sseldi
    #
    xnegcld
    xaddcld
    #
    @29
    wph
    @2
    @13
    @8
    cle
    @14
    wph
    @13
    cn
    @11
    cM
    cfv
    #
    vk
    cesum
    #
    @8
    @25
    wph
    @15
    cxr
    @32
    @16
    wph
    @18
    @31
    @15
    wcel
    #
    vk
    cn
    wral
    @32
    @15
    wcel
    @19
    wph
    @33
    vk
    cn
    @22
    @17
    @15
    @11
    cM
    wph
    @17
    @15
    cM
    wf
    #
    @21
    carsgval.2
    adantr
    @24
    ffvelrnd
    #
    ralrimiva
    cn
    @31
    vk
    cvv
    vk
    cn
    nfcv
    esumcl
    syl2anc
    sseldi
    @30
    wph
    @13
    vk
    cn
    @11
    cmpt
    #
    crn
    #
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    #
    @32
    cle
    wph
    @13
    @37
    cuni
    #
    cM
    cfv
    #
    @40
    cle
    wph
    @12
    @41
    cM
    wph
    @11
    @17
    wcel
    #
    vk
    cn
    wral
    #
    @12
    @41
    wceq
    wph
    @43
    vk
    cn
    @24
    ralrimiva
    #
    vk
    cn
    @11
    @17
    dfiun3g
    syl
    fveq2d
    wph
    @37
    com
    cdom
    wbr
    #
    @37
    @17
    wss
    #
    @42
    @40
    cle
    wbr
    #
    @46
    wph
    cn
    com
    cdom
    wbr
    @36
    com
    cdom
    wbr
    @46
    nnct
    vk
    cn
    @11
    mptct
    @36
    rnct
    mp2b
    a1i
    wph
    @44
    @47
    @45
    vk
    cn
    @11
    @17
    @36
    @36
    eqid
    rnmptss
    syl
    @37
    cvv
    wcel
    #
    wph
    @46
    @47
    w3a
    #
    @48
    wi
    #
    @18
    @36
    cvv
    wcel
    @49
    nnex
    vk
    cn
    @11
    cvv
    mptexg
    @36
    cvv
    rnexg
    mp2b
    wph
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @52
    @17
    wss
    #
    w3a
    #
    @52
    cuni
    #
    cM
    cfv
    #
    @52
    @39
    vy
    cesum
    #
    cle
    wbr
    #
    wi
    @51
    vx
    @37
    cvv
    @52
    @37
    wceq
    #
    @55
    @50
    @59
    @48
    @60
    @53
    @46
    @54
    @47
    wph
    @52
    @37
    com
    cdom
    breq1
    @52
    @37
    @17
    sseq1
    3anbi23d
    @60
    @57
    @42
    @58
    @40
    cle
    @60
    @56
    @41
    cM
    @52
    @37
    unieq
    fveq2d
    @52
    @37
    @39
    vy
    esumeq1
    breq12d
    imbi12d
    carsgsiga.2
    vtoclg
    ax-mp
    mpd3an23
    eqbrtrd
    wph
    vy
    cn
    @11
    @39
    @31
    vk
    cvv
    @17
    @38
    @11
    cM
    fveq2
    @19
    @35
    @24
    @22
    @11
    c0
    wceq
    #
    wa
    #
    @31
    c0
    cM
    cfv
    #
    cc0
    @62
    @11
    c0
    cM
    @22
    @61
    simpr
    fveq2d
    wph
    @63
    cc0
    wceq
    #
    @21
    @61
    carsgsiga.1
    ad2antrr
    eqtrd
    wph
    vk
    cn
    cA
    cE
    cin
    #
    wdisj
    #
    vk
    cn
    @11
    wdisj
    #
    wph
    vk
    cn
    cA
    wdisj
    #
    @66
    carsgclctunlem2.1
    vk
    cE
    cn
    cA
    disjin
    syl
    @65
    @11
    wceq
    #
    vk
    cn
    wral
    @66
    @67
    wb
    @69
    vk
    cn
    cA
    cE
    incom
    rgenw
    vk
    cn
    @65
    @11
    disjeq2
    ax-mp
    sylib
    esumrnmpt2
    breqtrd
    wph
    @31
    @8
    vk
    vn
    wph
    @6
    @4
    @26
    @28
    wph
    vx
    vy
    @3
    cE
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    wph
    cE
    @0
    difssd
    carsgclctunlem2.3
    carsgsiga.3
    carsgmon
    #
    xrge0subcld
    @35
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    c1
    @71
    cfz
    co
    #
    @31
    vk
    cesum
    #
    @6
    cE
    vk
    @74
    cA
    ciun
    #
    cdif
    #
    cM
    cfv
    #
    cxne
    #
    cxad
    co
    #
    @8
    cle
    @73
    cE
    @76
    cin
    #
    cM
    cfv
    #
    @78
    cxad
    co
    #
    @79
    cxad
    co
    #
    @82
    @80
    @75
    @73
    @84
    @82
    @78
    @79
    cxad
    co
    #
    cxad
    co
    #
    @82
    cc0
    cxad
    co
    #
    @82
    @73
    @82
    cxr
    wcel
    #
    @82
    cmnf
    wne
    #
    @78
    cxr
    wcel
    #
    @78
    cmnf
    wne
    #
    @79
    cxr
    wcel
    #
    @79
    cmnf
    wne
    @84
    @86
    wceq
    @73
    @15
    cxr
    @82
    @16
    @73
    @17
    @15
    @81
    cM
    wph
    @34
    @72
    carsgval.2
    adantr
    #
    @73
    cE
    @76
    cO
    wph
    @23
    @72
    carsgclctunlem2.3
    adantr
    #
    elpwincl1
    ffvelrnd
    #
    sseldi
    #
    @73
    @82
    @15
    wcel
    @89
    @95
    @82
    xrge0neqmnf
    syl
    #
    @73
    @15
    cxr
    @78
    @16
    @73
    @17
    @15
    @77
    cM
    @93
    @73
    cE
    @76
    cO
    @94
    elpwdifcl
    #
    ffvelrnd
    #
    sseldi
    #
    @73
    @78
    @15
    wcel
    @91
    @99
    @78
    xrge0neqmnf
    syl
    @73
    @78
    @100
    xnegcld
    #
    @73
    @79
    cmnf
    @73
    @79
    cmnf
    wceq
    #
    @6
    cpnf
    wceq
    @73
    @102
    wa
    #
    @83
    @82
    cpnf
    cxad
    co
    #
    @6
    cpnf
    @103
    @78
    cpnf
    @82
    cxad
    @103
    @79
    cxne
    #
    @78
    cpnf
    @73
    @105
    @78
    wceq
    #
    @102
    @73
    @90
    @106
    @100
    @78
    xnegneg
    syl
    adantr
    @103
    @105
    cmnf
    cxne
    #
    cpnf
    @102
    @105
    @107
    wceq
    @73
    @79
    cmnf
    xnegeq
    adantl
    xnegmnf
    syl6eq
    eqtr3d
    oveq2d
    @73
    @83
    @6
    wceq
    #
    @102
    @73
    @23
    ve
    cv
    #
    @76
    cin
    #
    cM
    cfv
    #
    @109
    @76
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @109
    cM
    cfv
    #
    wceq
    #
    ve
    @17
    wral
    #
    @108
    @94
    @73
    @76
    cO
    wss
    #
    @117
    @73
    @76
    cM
    ccarsg
    cfv
    #
    wcel
    @118
    @117
    wa
    @73
    @76
    vk
    @74
    cA
    cmpt
    #
    crn
    #
    cuni
    #
    @119
    @73
    cA
    @119
    wcel
    #
    vk
    @74
    wral
    #
    @76
    @122
    wceq
    @73
    @123
    vk
    @74
    @73
    @20
    @74
    wcel
    #
    wa
    #
    wph
    @21
    @123
    wph
    @72
    @125
    simpll
    #
    @73
    @74
    cn
    @20
    @74
    cn
    wss
    #
    @73
    @71
    fz1ssnn
    #
    a1i
    #
    sselda
    #
    carsgclctunlem2.2
    syl2anc
    #
    ralrimiva
    #
    vk
    @74
    cA
    @119
    dfiun3g
    syl
    #
    @73
    vx
    vy
    @121
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    @72
    carsgval.1
    adantr
    #
    @93
    wph
    @64
    @72
    carsgsiga.1
    adantr
    #
    wph
    @53
    @54
    @59
    @72
    carsgsiga.2
    3adant1r
    #
    @121
    cfn
    wcel
    #
    @73
    @74
    cfn
    wcel
    @120
    cfn
    wcel
    @138
    c1
    @71
    fzfi
    #
    vk
    @74
    cA
    mptfi
    @120
    rnfi
    mp2b
    a1i
    #
    @73
    @124
    @121
    @119
    wss
    @133
    vk
    @74
    cA
    @119
    @120
    @120
    eqid
    rnmptss
    syl
    #
    fiunelcarsg
    eqeltrd
    @73
    @76
    ve
    cM
    cO
    cV
    @135
    @93
    elcarsg
    mpbid
    simprd
    @116
    @108
    ve
    cE
    @17
    @109
    cE
    wceq
    #
    @114
    @83
    @115
    @6
    @142
    @111
    @82
    @113
    @78
    cxad
    @142
    @110
    @81
    cM
    @109
    cE
    @76
    ineq1
    fveq2d
    @142
    @112
    @77
    cM
    @109
    cE
    @76
    difeq1
    fveq2d
    oveq12d
    @109
    cE
    cM
    fveq2
    eqeq12d
    rspcv
    sylc
    #
    adantr
    @73
    @104
    cpnf
    wceq
    #
    @102
    @73
    @88
    @89
    @144
    @96
    @97
    @82
    xaddpnf1
    syl2anc
    adantr
    3eqtr3d
    @103
    @6
    cpnf
    wph
    @6
    cpnf
    wne
    @72
    @102
    carsgclctunlem2.4
    ad2antrr
    neneqd
    pm2.65da
    neqned
    @82
    @78
    @79
    xaddass
    syl222anc
    @73
    @85
    cc0
    @82
    cxad
    @73
    @90
    @85
    cc0
    wceq
    @100
    @78
    xnegid
    syl
    oveq2d
    @73
    @88
    @87
    @82
    wceq
    @96
    @82
    xaddid1
    syl
    3eqtrd
    @73
    @83
    @6
    @79
    cxad
    @143
    oveq1d
    @73
    @82
    cE
    @122
    cin
    #
    cM
    cfv
    @121
    cE
    @38
    cin
    #
    cM
    cfv
    #
    vy
    cesum
    @75
    @73
    @81
    @145
    cM
    @73
    @76
    @122
    cE
    @134
    ineq2d
    fveq2d
    @73
    vx
    vy
    @121
    cE
    cM
    cO
    cV
    @135
    @93
    @136
    @137
    @140
    @141
    @73
    @121
    vk
    cn
    cA
    cmpt
    #
    crn
    #
    wss
    #
    vy
    @149
    @38
    wdisj
    #
    vy
    @121
    @38
    wdisj
    @150
    @73
    @128
    @120
    @148
    wss
    @150
    @129
    vk
    @74
    cn
    cA
    mptss
    @120
    @148
    rnss
    mp2b
    a1i
    wph
    @151
    @72
    wph
    @68
    @151
    carsgclctunlem2.1
    vk
    vy
    cn
    cA
    disjrnmpt
    syl
    adantr
    vy
    @121
    @149
    @38
    disjss1
    sylc
    @94
    carsgclctunlem1
    @73
    vy
    @74
    cA
    @147
    @31
    vk
    cvv
    @119
    @38
    cA
    wceq
    @146
    @11
    cM
    @38
    cA
    cE
    ineq2
    fveq2d
    @74
    cvv
    wcel
    @73
    @74
    cfn
    @139
    elexi
    a1i
    @126
    wph
    @21
    @33
    @127
    @131
    @35
    syl2anc
    @132
    @126
    cA
    c0
    wceq
    #
    wa
    #
    @31
    @63
    cc0
    @153
    @11
    c0
    cM
    @152
    @61
    @126
    @152
    @11
    c0
    wss
    #
    @61
    @152
    @11
    cA
    wss
    @154
    cE
    cA
    inss2
    cA
    c0
    @11
    sseq2
    mpbii
    @11
    ss0
    syl
    adantl
    fveq2d
    @73
    @64
    @125
    @152
    @136
    ad2antrr
    eqtrd
    @73
    @128
    @68
    vk
    @74
    cA
    wdisj
    @130
    wph
    @68
    @72
    carsgclctunlem2.1
    adantr
    vk
    @74
    cn
    cA
    disjss1
    sylc
    esumrnmpt2
    3eqtrd
    3eqtr3rd
    @73
    @92
    @7
    cxr
    wcel
    @6
    cxr
    wcel
    #
    @79
    @7
    cle
    wbr
    #
    @80
    @8
    cle
    wbr
    @101
    @73
    @4
    @73
    @15
    cxr
    @4
    @16
    wph
    @4
    @15
    wcel
    #
    @72
    @28
    adantr
    sseldi
    #
    xnegcld
    wph
    @155
    @72
    @27
    adantr
    @73
    @10
    @90
    @4
    @78
    cle
    wbr
    #
    @156
    @158
    @100
    @73
    vx
    vy
    @3
    @77
    cM
    cO
    cV
    @135
    @93
    @73
    @76
    @0
    cE
    @128
    @76
    @0
    wss
    @73
    @129
    vk
    @74
    cn
    cA
    iunss1
    mp1i
    sscond
    @98
    wph
    @52
    @38
    wss
    @38
    @17
    wcel
    @52
    cM
    cfv
    @39
    cle
    wbr
    @72
    carsgsiga.3
    3adant1r
    carsgmon
    @10
    @90
    wa
    @159
    @156
    @4
    @78
    xleneg
    biimpa
    syl21anc
    @79
    @7
    @6
    xleadd2a
    syl31anc
    eqbrtrd
    esumgect
    xrletrd
    syl5eqbrr
    @2
    @8
    @4
    xleadd1a
    syl31anc
    wph
    @6
    @15
    wcel
    @157
    @4
    @6
    cle
    wbr
    @9
    @6
    wceq
    @26
    @28
    @70
    @6
    @4
    xrge0npcan
    syl3anc
    breqtrd
end
