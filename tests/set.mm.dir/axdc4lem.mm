include "wcel.mm"
include "com.mm"
include "cxp.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "wceq.mm"
include "csuc.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "co.mm"
include "peano1.mm"
include "opelxpi.mm"
include "mpan.mm"
include "simp2.mm"
include "fovrn.mm"
include "wss.mm"
include "peano2.mm"
include "snssd.mm"
include "eldifi.mm"
include "elpw2.mm"
include "xpss12.mm"
include "sylan2b.mm"
include "syl2an.mm"
include "snex.mm"
include "ovex.mm"
include "xpex.mm"
include "elpw.mm"
include "sylibr.mm"
include "syl2anc.mm"
include "wn.mm"
include "eldifn.mm"
include "wne.mm"
include "elsn.mm"
include "necon3bbii.mm"
include "vex.mm"
include "sucex.mm"
include "snnz.mm"
include "xpnz.mm"
include "biimpi.mm"
include "sylbi.mm"
include "3syl.mm"
include "eldifd.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "fmpt2.mm"
include "sylib.mm"
include "dcomex.mm"
include "axdc3.mm"
include "wi.mm"
include "c2nd.mm"
include "ccom.mm"
include "cvv.mm"
include "2ndcof.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "fex2.mm"
include "mp3an23.mm"
include "syl.mm"
include "fvco3.mm"
include "mpan2.mm"
include "fveq2.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "op2ndg.mm"
include "sylan9eqr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfan.mm"
include "opeq1.mm"
include "eqeq12d.mm"
include "exbidv.mm"
include "weq.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "imp.mm"
include "3ad2antr2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "simplr.mm"
include "ffvelrn.mm"
include "eleq1.mm"
include "opelxp2.mm"
include "syl6bi.mm"
include "mpan9.mm"
include "suceq.mm"
include "sneqd.mm"
include "oveq1.mm"
include "xpeq12d.mm"
include "oveq2.mm"
include "xpeq2d.mm"
include "ovmpt2.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "ad2antlr.mm"
include "eleq2.mm"
include "elxp.mm"
include "velsn.mm"
include "biimpac.mm"
include "adantrr.mm"
include "eximi.mm"
include "exlimiv.mm"
include "sylsyld.mm"
include "expcom.mm"
include "com3l.mm"
include "cbvexv.mm"
include "syl8ib.mm"
include "impancom.mm"
include "3adant2.mm"
include "com12.mm"
include "finds2.mm"
include "ralrimiv.mm"
include "rspccv.mm"
include "3impia.mm"
include "simp21.mm"
include "simp3.mm"
include "rspa.mm"
include "3ad2antl3.mm"
include "3adant1.mm"
include "simpl.mm"
include "simprr.mm"
include "syl5.mm"
include "syl5eqr.mm"
include "eleq2d.mm"
include "sylan2.mm"
include "simpll.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "biimprcd.mm"
include "exp4c.mm"
include "impcom.mm"
include "exlimivv.mm"
include "sylbid.mm"
include "ex.mm"
include "3imp.mm"
include "syl121anc.mm"
include "3expia.mm"
include "ralrimi.mm"
include "3jca.mm"
include "feq1.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "sylc.mm"
include "exlimdv.mm"
include "adantr.mm"
include "mpd.mm"

theorem axdc4lem
  let vx: setvar x
  let cA: class A
  let cC: class C
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vh: setvar h
  let vi: setvar i
  let vm: setvar m
  let vs: setvar s
  let vt: setvar t
  let vz: setvar z
  assume axdc4lem.1: |- A e. _V
  assume axdc4lem.2: |- G = ( n e. _om , x e. A |-> ( { suc n } X. ( n F x ) ) )

  disjoint g k
  disjoint g n
  disjoint g x
  disjoint A g
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint C g
  disjoint C k
  disjoint F g
  disjoint F n
  disjoint F x
  disjoint G k
  disjoint g h
  disjoint g i
  disjoint g m
  disjoint g s
  disjoint g t
  disjoint g z
  disjoint h i
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h z
  disjoint A h
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i z
  disjoint A i
  disjoint k m
  disjoint k s
  disjoint k t
  disjoint k z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n t
  disjoint n z
  disjoint s t
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint A z
  disjoint C h
  disjoint C i
  disjoint C m
  disjoint C z
  disjoint F h
  disjoint F s
  disjoint F t
  disjoint F z
  disjoint G h
  disjoint G i
  disjoint G m
  disjoint G z
  assert |- ( ( C e. A /\ F : ( _om X. A ) --> ( ~P A \ { (/) } ) ) -> E. g ( g : _om --> A /\ ( g ` (/) ) = C /\ A. k e. _om ( g ` suc k ) e. ( k F ( g ` k ) ) ) )

  proof
    cC
    cA
    wcel
    #
    com
    cA
    cxp
    #
    cA
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cF
    wf
    #
    wa
    com
    @1
    vh
    cv
    #
    wf
    #
    c0
    @6
    cfv
    #
    c0
    cC
    cop
    #
    wceq
    #
    vk
    cv
    #
    csuc
    #
    @6
    cfv
    #
    @11
    @6
    cfv
    #
    cG
    cfv
    #
    wcel
    #
    vk
    com
    wral
    #
    w3a
    #
    vh
    wex
    #
    com
    cA
    vg
    cv
    #
    wf
    #
    c0
    @20
    cfv
    #
    cC
    wceq
    #
    @12
    @20
    cfv
    #
    @11
    @11
    @20
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    com
    wral
    #
    w3a
    #
    vg
    wex
    #
    @0
    @9
    @1
    wcel
    #
    @1
    @1
    cpw
    #
    @3
    cdif
    #
    cG
    wf
    #
    @19
    @5
    c0
    com
    wcel
    #
    @0
    @31
    peano1
    c0
    cC
    com
    cA
    opelxpi
    mpan
    @5
    vn
    cv
    #
    csuc
    #
    csn
    #
    @36
    vx
    cv
    #
    cF
    co
    #
    cxp
    #
    @33
    wcel
    #
    vx
    cA
    wral
    vn
    com
    wral
    @34
    @5
    @42
    vn
    vx
    com
    cA
    @5
    @36
    com
    wcel
    #
    @39
    cA
    wcel
    #
    @42
    @5
    @43
    @44
    w3a
    #
    @41
    @32
    @3
    @45
    @43
    @40
    @4
    wcel
    #
    @41
    @32
    wcel
    #
    @5
    @43
    @44
    simp2
    @36
    @39
    @4
    com
    cA
    cF
    fovrn
    #
    @43
    @46
    wa
    @41
    @1
    wss
    #
    @47
    @43
    @38
    com
    wss
    #
    @40
    @2
    wcel
    #
    @49
    @46
    @43
    @37
    com
    @36
    peano2
    snssd
    @40
    @2
    @3
    eldifi
    @51
    @50
    @40
    cA
    wss
    @49
    @40
    cA
    axdc4lem.1
    elpw2
    @38
    com
    @40
    cA
    xpss12
    sylan2b
    syl2an
    @41
    @1
    @38
    @40
    @37
    snex
    @36
    @39
    cF
    ovex
    #
    xpex
    #
    elpw
    sylibr
    syl2anc
    @45
    @46
    @40
    @3
    wcel
    #
    wn
    #
    @41
    @3
    wcel
    #
    wn
    #
    @48
    @40
    @2
    @3
    eldifn
    @55
    @41
    c0
    wne
    #
    @57
    @55
    @40
    c0
    wne
    #
    @58
    @54
    @40
    c0
    @40
    c0
    @52
    elsn
    necon3bbii
    @38
    c0
    wne
    #
    @59
    @58
    @37
    @36
    vn
    vex
    sucex
    snnz
    @60
    @59
    wa
    @58
    @38
    @40
    xpnz
    biimpi
    mpan
    sylbi
    @56
    @41
    c0
    @41
    c0
    @53
    elsn
    necon3bbii
    sylibr
    3syl
    eldifd
    3expib
    ralrimivv
    vn
    vx
    com
    cA
    @41
    @33
    cG
    axdc4lem.2
    fmpt2
    sylib
    @1
    @9
    vh
    vk
    cG
    com
    cA
    dcomex
    axdc4lem.1
    xpex
    axdc3
    syl2an
    @0
    @19
    @30
    wi
    @5
    @0
    @18
    @30
    vh
    @0
    @18
    @30
    @0
    @18
    wa
    #
    c2nd
    @6
    ccom
    #
    cvv
    wcel
    #
    com
    cA
    @62
    wf
    #
    c0
    @62
    cfv
    #
    cC
    wceq
    #
    @12
    @62
    cfv
    #
    @11
    @11
    @62
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    com
    wral
    #
    w3a
    #
    @30
    @61
    @64
    @63
    @18
    @64
    @0
    @7
    @10
    @64
    @17
    com
    com
    cA
    @6
    2ndcof
    3ad2ant1
    adantl
    #
    @64
    com
    cvv
    wcel
    cA
    cvv
    wcel
    @63
    dcomex
    axdc4lem.1
    com
    cA
    @62
    cvv
    cvv
    fex2
    mp3an23
    syl
    @61
    @64
    @66
    @71
    @73
    @18
    @0
    @65
    @9
    c2nd
    cfv
    #
    cC
    @18
    @65
    @8
    c2nd
    cfv
    #
    @74
    @7
    @10
    @65
    @75
    wceq
    #
    @17
    @7
    @35
    @76
    peano1
    com
    @1
    c0
    c2nd
    @6
    fvco3
    mpan2
    3ad2ant1
    @10
    @7
    @75
    @74
    wceq
    @17
    @8
    @9
    c2nd
    fveq2
    3ad2ant2
    eqtrd
    @35
    @0
    @74
    cC
    wceq
    peano1
    c0
    cC
    com
    cA
    op2ndg
    mpan
    sylan9eqr
    @61
    @70
    vk
    com
    @0
    @18
    vk
    @0
    vk
    nfv
    @7
    @10
    @17
    vk
    @7
    vk
    nfv
    @10
    vk
    nfv
    @16
    vk
    com
    nfra1
    nf3an
    nfan
    @0
    @18
    @11
    com
    wcel
    #
    @70
    @0
    @18
    @77
    w3a
    @14
    @11
    vz
    cv
    #
    cop
    #
    wceq
    #
    vz
    wex
    #
    @7
    @77
    @16
    @70
    @0
    @18
    @77
    @81
    @61
    vm
    cv
    #
    @6
    cfv
    #
    @82
    @78
    cop
    #
    wceq
    #
    vz
    wex
    #
    vm
    com
    wral
    @77
    @81
    wi
    @61
    @86
    vm
    com
    @82
    com
    wcel
    @61
    @86
    @86
    @8
    c0
    @78
    cop
    #
    wceq
    #
    vz
    wex
    #
    vi
    cv
    #
    @6
    cfv
    #
    @90
    @78
    cop
    #
    wceq
    #
    vz
    wex
    #
    @90
    csuc
    #
    @6
    cfv
    #
    @95
    @78
    cop
    #
    wceq
    #
    vz
    wex
    #
    @61
    vm
    vi
    @82
    c0
    wceq
    #
    @85
    @88
    vz
    @100
    @83
    @8
    @84
    @87
    @82
    c0
    @6
    fveq2
    @82
    c0
    @78
    opeq1
    eqeq12d
    exbidv
    vm
    vi
    weq
    #
    @85
    @93
    vz
    @101
    @83
    @91
    @84
    @92
    @82
    @90
    @6
    fveq2
    @82
    @90
    @78
    opeq1
    eqeq12d
    exbidv
    @82
    @95
    wceq
    #
    @85
    @98
    vz
    @102
    @83
    @96
    @84
    @97
    @82
    @95
    @6
    fveq2
    @82
    @95
    @78
    opeq1
    eqeq12d
    exbidv
    @0
    @7
    @10
    @89
    @17
    @0
    @10
    @89
    @88
    @10
    vz
    cC
    cA
    @78
    cC
    wceq
    @87
    @9
    @8
    @78
    cC
    c0
    opeq2
    eqeq2d
    spcegv
    imp
    3ad2antr2
    @61
    @90
    com
    wcel
    #
    @94
    @99
    wi
    #
    @18
    @103
    @104
    wi
    #
    @0
    @7
    @17
    @105
    @10
    @7
    @103
    @17
    @104
    @7
    @103
    wa
    #
    @17
    @94
    @96
    @95
    vt
    cv
    #
    cop
    #
    wceq
    #
    vt
    wex
    #
    @99
    @94
    @106
    @17
    @110
    @93
    @106
    @17
    @110
    wi
    #
    wi
    vz
    @106
    @93
    @111
    @106
    @93
    wa
    #
    @91
    cG
    cfv
    #
    @95
    csn
    #
    @90
    @78
    cF
    co
    #
    cxp
    #
    wceq
    #
    @17
    @96
    @113
    wcel
    #
    @110
    @112
    @113
    @90
    @78
    cG
    co
    #
    @116
    @93
    @113
    @119
    wceq
    @106
    @93
    @113
    @92
    cG
    cfv
    @119
    @91
    @92
    cG
    fveq2
    @90
    @78
    cG
    df-ov
    syl6eqr
    adantl
    @112
    @103
    @78
    cA
    wcel
    #
    @119
    @116
    wceq
    @7
    @103
    @93
    simplr
    @106
    @91
    @1
    wcel
    #
    @93
    @120
    com
    @1
    @90
    @6
    ffvelrn
    @93
    @121
    @92
    @1
    wcel
    @120
    @91
    @92
    @1
    eleq1
    @90
    @78
    com
    cA
    opelxp2
    syl6bi
    mpan9
    vn
    vx
    @90
    @78
    com
    cA
    @41
    @116
    cG
    @114
    @90
    @39
    cF
    co
    #
    cxp
    vn
    vi
    weq
    #
    @38
    @114
    @40
    @122
    @123
    @37
    @95
    @36
    @90
    suceq
    sneqd
    @36
    @90
    @39
    cF
    oveq1
    xpeq12d
    vx
    vz
    weq
    #
    @122
    @115
    @114
    @39
    @78
    @90
    cF
    oveq2
    xpeq2d
    axdc4lem.2
    @114
    @115
    @95
    snex
    @90
    @78
    cF
    ovex
    xpex
    ovmpt2
    syl2anc
    eqtrd
    @103
    @17
    @118
    wi
    @7
    @93
    @16
    @118
    vk
    @90
    com
    vk
    vi
    weq
    #
    @13
    @96
    @15
    @113
    @125
    @12
    @95
    @6
    @11
    @90
    suceq
    fveq2d
    @125
    @14
    @91
    cG
    @11
    @90
    @6
    fveq2
    fveq2d
    eleq12d
    rspcv
    ad2antlr
    @117
    @118
    @96
    @116
    wcel
    #
    @110
    @113
    @116
    @96
    eleq2
    @126
    @96
    vs
    cv
    #
    @107
    cop
    #
    wceq
    #
    @127
    @114
    wcel
    #
    @107
    @115
    wcel
    #
    wa
    wa
    #
    vt
    wex
    #
    vs
    wex
    @110
    vs
    vt
    @96
    @114
    @115
    elxp
    @133
    @110
    vs
    @132
    @109
    vt
    @129
    @130
    @109
    @131
    @130
    @129
    @109
    @130
    @128
    @108
    @96
    @130
    @127
    @95
    wceq
    @128
    @108
    wceq
    vs
    @95
    velsn
    @127
    @95
    @107
    opeq1
    sylbi
    eqeq2d
    biimpac
    adantrr
    eximi
    exlimiv
    sylbi
    syl6bi
    sylsyld
    expcom
    exlimiv
    com3l
    @109
    @98
    vt
    vz
    vt
    vz
    weq
    @108
    @97
    @96
    @107
    @78
    @95
    opeq2
    eqeq2d
    cbvexv
    syl8ib
    impancom
    3adant2
    adantl
    com12
    finds2
    com12
    ralrimiv
    @86
    @81
    vm
    @11
    com
    vm
    vk
    weq
    #
    @85
    @80
    vz
    @134
    @83
    @14
    @84
    @79
    @82
    @11
    @6
    fveq2
    @82
    @11
    @78
    opeq1
    eqeq12d
    exbidv
    rspccv
    syl
    3impia
    @0
    @7
    @10
    @17
    @77
    simp21
    @0
    @18
    @77
    simp3
    @18
    @77
    @16
    @0
    @17
    @7
    @77
    @16
    @10
    @16
    vk
    com
    rspa
    3ad2antl3
    3adant1
    @81
    @7
    @77
    wa
    #
    @16
    @70
    @80
    @135
    @16
    @70
    wi
    #
    wi
    vz
    @80
    @135
    @136
    @80
    @135
    wa
    #
    @16
    @13
    @12
    csn
    #
    @11
    @78
    cF
    co
    #
    cxp
    #
    wcel
    #
    @70
    @137
    @15
    @140
    @13
    @137
    @15
    @79
    cG
    cfv
    #
    @140
    @137
    @14
    @79
    cG
    @80
    @135
    simpl
    fveq2d
    @137
    @77
    @120
    @142
    @140
    wceq
    @80
    @7
    @77
    simprr
    @80
    @135
    @120
    @135
    @14
    @1
    wcel
    #
    @80
    @120
    com
    @1
    @11
    @6
    ffvelrn
    @80
    @143
    @79
    @1
    wcel
    @120
    @14
    @79
    @1
    eleq1
    @11
    @78
    com
    cA
    opelxp2
    syl6bi
    syl5
    imp
    @77
    @120
    wa
    @142
    @11
    @78
    cG
    co
    @140
    @11
    @78
    cG
    df-ov
    vn
    vx
    @11
    @78
    com
    cA
    @41
    @140
    cG
    @138
    @11
    @39
    cF
    co
    #
    cxp
    vn
    vk
    weq
    #
    @38
    @138
    @40
    @144
    @145
    @37
    @12
    @36
    @11
    suceq
    sneqd
    @36
    @11
    @39
    cF
    oveq1
    xpeq12d
    @124
    @144
    @139
    @138
    @39
    @78
    @11
    cF
    oveq2
    xpeq2d
    axdc4lem.2
    @138
    @139
    @12
    snex
    @11
    @78
    cF
    ovex
    xpex
    ovmpt2
    syl5eqr
    syl2anc
    eqtrd
    eleq2d
    @80
    @135
    @141
    @70
    wi
    @141
    @80
    @135
    @70
    @141
    @13
    @128
    wceq
    #
    @127
    @138
    wcel
    #
    @107
    @139
    wcel
    #
    wa
    #
    wa
    #
    vt
    wex
    vs
    wex
    @80
    @135
    @70
    wi
    wi
    #
    vs
    vt
    @13
    @138
    @139
    elxp
    @150
    @151
    vs
    vt
    @149
    @146
    @151
    @148
    @146
    @151
    wi
    @147
    @148
    @146
    @80
    @135
    @70
    @146
    @80
    wa
    #
    @135
    wa
    #
    @70
    @148
    @153
    @67
    @107
    @69
    @139
    @153
    @67
    @128
    c2nd
    cfv
    #
    @107
    @153
    @67
    @13
    c2nd
    cfv
    #
    @154
    @135
    @67
    @155
    wceq
    #
    @152
    @77
    @7
    @12
    com
    wcel
    @156
    @11
    peano2
    com
    @1
    @12
    c2nd
    @6
    fvco3
    sylan2
    adantl
    @153
    @13
    @128
    c2nd
    @146
    @80
    @135
    simpll
    fveq2d
    eqtrd
    @127
    @107
    vs
    vex
    vt
    vex
    op2nd
    syl6eq
    @153
    @68
    @78
    @11
    cF
    @153
    @68
    @79
    c2nd
    cfv
    #
    @78
    @153
    @68
    @14
    c2nd
    cfv
    #
    @157
    @135
    @68
    @158
    wceq
    @152
    com
    @1
    @11
    c2nd
    @6
    fvco3
    adantl
    @153
    @14
    @79
    c2nd
    @146
    @80
    @135
    simplr
    fveq2d
    eqtrd
    @11
    @78
    vk
    vex
    vz
    vex
    op2nd
    syl6eq
    oveq2d
    eleq12d
    biimprcd
    exp4c
    adantl
    impcom
    exlimivv
    sylbi
    com3l
    imp
    sylbid
    ex
    exlimiv
    3imp
    syl121anc
    3expia
    ralrimi
    3jca
    @29
    @72
    vg
    @62
    cvv
    @20
    @62
    wceq
    #
    @21
    @64
    @23
    @66
    @28
    @71
    com
    cA
    @20
    @62
    feq1
    @159
    @22
    @65
    cC
    c0
    @20
    @62
    fveq1
    eqeq1d
    @159
    @27
    @70
    vk
    com
    @159
    @24
    @67
    @26
    @69
    @12
    @20
    @62
    fveq1
    @159
    @25
    @68
    @11
    cF
    @11
    @20
    @62
    fveq1
    oveq2d
    eleq12d
    ralbidv
    3anbi123d
    spcegv
    sylc
    ex
    exlimdv
    adantr
    mpd
end
