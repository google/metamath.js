include "wcel.mm"
include "cwun.mm"
include "wss.mm"
include "wtr.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "cfv.mm"
include "com.mm"
include "wrex.mm"
include "crn.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "cun.mm"
include "cmpt.mm"
include "ciun.mm"
include "c1o.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnunirn.mm"
include "ax-mp.mm"
include "bitri.mm"
include "wa.mm"
include "csuc.mm"
include "elssuni.mm"
include "ad2antll.mm"
include "ssun2.mm"
include "ssun1.mm"
include "sstri.mm"
include "syl6ss.mm"
include "wceq.mm"
include "simprl.mm"
include "fvex.mm"
include "uniex.mm"
include "unex.mm"
include "prex.mm"
include "mptex.mm"
include "rnex.mm"
include "iunex.mm"
include "weq.mm"
include "id.mm"
include "unieq.mm"
include "uneq12d.mm"
include "pweq.mm"
include "preq12d.mm"
include "preq2.mm"
include "cbvmptv.mm"
include "preq1.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "cbviunv.mm"
include "mpteq1.mm"
include "uneq2d.mm"
include "iuneq12d.mm"
include "frsucmpt2.mm"
include "sylancl.mm"
include "sseqtr4d.mm"
include "fvssunirn.mm"
include "sseqtr4i.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "dftr3.mm"
include "sylibr.mm"
include "con0.mm"
include "1on.mm"
include "unexg.mm"
include "mpan2.mm"
include "fveq1i.mm"
include "fr0g.mm"
include "syl.mm"
include "syl6eqssr.mm"
include "unssbd.mm"
include "1n0.mm"
include "ssn0.mm"
include "ssiun2s.mm"
include "syl5sseqr.mm"
include "sstrd.mm"
include "unssad.mm"
include "vpwex.mm"
include "vuniex.mm"
include "prss.mm"
include "simprd.mm"
include "simpld.mm"
include "simplrl.mm"
include "word.mm"
include "ordom.mm"
include "ordunel.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "ssid.mm"
include "a1i.mm"
include "suceq.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "vtoclga.mm"
include "ad2antrr.mm"
include "sstr2.mm"
include "syl5com.mm"
include "findsg.mm"
include "simplrr.mm"
include "sseldd.mm"
include "wi.mm"
include "biantrud.mm"
include "bicomd.mm"
include "imbi12d.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "sseq1d.mm"
include "chvarv.mm"
include "expl.mm"
include "sylc.mm"
include "simprr.mm"
include "eqid.mm"
include "elrnmpt1s.mm"
include "3jca.mm"
include "wfun.mm"
include "rdgfun.mm"
include "omex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "iswun.mm"
include "syl3anbrc.mm"
include "jca.mm"

theorem wunex2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cU: class U
  let cF: class F
  let cV: class V
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vi: setvar i
  let vk: setvar k
  assume wunex2.f: |- F = ( rec ( ( z e. _V |-> ( ( z u. U. z ) u. U_ x e. z ( { ~P x , U. x } u. ran ( y e. z |-> { x , y } ) ) ) ) , ( A u. 1o ) ) |` _om )
  assume wunex2.u: |- U = U. ran F

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint A a
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint A b
  disjoint m n
  disjoint m w
  disjoint A m
  disjoint n w
  disjoint A n
  disjoint A w
  disjoint U a
  disjoint U b
  disjoint U m
  disjoint U n
  disjoint V a
  disjoint V b
  disjoint V m
  disjoint V n
  disjoint b i
  disjoint b k
  disjoint b u
  disjoint b v
  disjoint F b
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint F i
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint F k
  disjoint m u
  disjoint m v
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint F w
  assert |- ( A e. V -> ( U e. WUni /\ A C_ U ) )

  proof
    cA
    cV
    wcel
    #
    cU
    cwun
    wcel
    #
    cA
    cU
    wss
    @0
    cU
    wtr
    #
    cU
    c0
    wne
    #
    va
    cv
    #
    cuni
    #
    cU
    wcel
    #
    @4
    cpw
    #
    cU
    wcel
    #
    @4
    vb
    cv
    #
    cpr
    #
    cU
    wcel
    #
    vb
    cU
    wral
    #
    w3a
    #
    va
    cU
    wral
    #
    @1
    @0
    @4
    cU
    wss
    #
    va
    cU
    wral
    @2
    @0
    @15
    va
    cU
    @4
    cU
    wcel
    #
    @4
    vm
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vm
    com
    wrex
    #
    @0
    @15
    @16
    @4
    cF
    crn
    #
    cuni
    #
    wcel
    #
    @20
    cU
    @22
    @4
    wunex2.u
    eleq2i
    cF
    com
    wfn
    #
    @23
    @20
    wb
    @24
    vz
    cvv
    vz
    cv
    #
    @25
    cuni
    #
    cun
    #
    vx
    @25
    vx
    cv
    #
    cpw
    #
    @28
    cuni
    #
    cpr
    #
    vy
    @25
    @28
    vy
    cv
    #
    cpr
    #
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    #
    cmpt
    #
    cA
    c1o
    cun
    #
    crdg
    #
    com
    cres
    #
    com
    wfn
    @40
    @39
    frfnom
    com
    cF
    @42
    wunex2.f
    fneq1i
    mpbir
    #
    vm
    @4
    cF
    com
    fnunirn
    ax-mp
    bitri
    #
    @0
    @19
    @15
    vm
    com
    @0
    @17
    com
    wcel
    #
    @19
    wa
    wa
    #
    @4
    @17
    csuc
    #
    cF
    cfv
    #
    cU
    @46
    @4
    @18
    @18
    cuni
    #
    cun
    #
    vu
    @18
    vu
    cv
    #
    cpw
    #
    @51
    cuni
    #
    cpr
    #
    vv
    @18
    @51
    vv
    cv
    #
    cpr
    #
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    #
    @48
    @46
    @4
    @49
    @61
    @19
    @4
    @49
    wss
    @0
    @45
    @4
    @18
    elssuni
    ad2antll
    @49
    @50
    @61
    @49
    @18
    ssun2
    @50
    @60
    ssun1
    #
    sstri
    syl6ss
    @46
    @45
    @61
    cvv
    wcel
    #
    @48
    @61
    wceq
    #
    @0
    @45
    @19
    simprl
    @50
    @60
    @18
    @49
    @17
    cF
    fvex
    #
    @18
    @65
    uniex
    unex
    vu
    @18
    @59
    @65
    @54
    @58
    @52
    @53
    prex
    #
    @57
    vv
    @18
    @56
    @65
    mptex
    rnex
    unex
    iunex
    unex
    #
    vz
    vw
    @40
    @17
    @38
    @61
    vw
    cv
    #
    @68
    cuni
    #
    cun
    #
    vu
    @68
    @54
    vv
    @68
    @56
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cun
    #
    cF
    cvv
    wunex2.f
    vw
    vz
    weq
    #
    @70
    @27
    @74
    @37
    @76
    @68
    @25
    @69
    @26
    @76
    id
    #
    @68
    @25
    unieq
    uneq12d
    @76
    @74
    vx
    @68
    @31
    vy
    @68
    @33
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    @37
    vu
    vx
    @68
    @73
    @80
    vu
    vx
    weq
    #
    @54
    @31
    @72
    @79
    @81
    @52
    @29
    @53
    @30
    @51
    @28
    pweq
    @51
    @28
    unieq
    preq12d
    @81
    @71
    @78
    @81
    @71
    vy
    @68
    @51
    @32
    cpr
    #
    cmpt
    @78
    vv
    vy
    @68
    @56
    @82
    @55
    @32
    @51
    preq2
    cbvmptv
    @81
    vy
    @68
    @82
    @33
    @51
    @28
    @32
    preq1
    mpteq2dv
    syl5eq
    rneqd
    uneq12d
    cbviunv
    @76
    vx
    @68
    @25
    @80
    @36
    @77
    @76
    @79
    @35
    @31
    @76
    @78
    @34
    vy
    @68
    @25
    @33
    mpteq1
    rneqd
    uneq2d
    iuneq12d
    syl5eq
    uneq12d
    #
    @68
    @18
    wceq
    #
    @70
    @50
    @74
    @60
    @84
    @68
    @18
    @69
    @49
    @84
    id
    #
    @68
    @18
    unieq
    uneq12d
    @84
    vu
    @68
    @18
    @73
    @59
    @85
    @84
    @72
    @58
    @54
    @84
    @71
    @57
    vv
    @68
    @18
    @56
    mpteq1
    rneqd
    uneq2d
    iuneq12d
    uneq12d
    frsucmpt2
    #
    sylancl
    #
    sseqtr4d
    @48
    @22
    cU
    cF
    @47
    fvssunirn
    wunex2.u
    sseqtr4i
    #
    syl6ss
    rexlimdvaa
    syl5bi
    ralrimiv
    va
    cU
    dftr3
    sylibr
    @0
    c1o
    cU
    wss
    c1o
    c0
    wne
    @3
    @0
    cA
    c1o
    cU
    @0
    @40
    c0
    cF
    cfv
    #
    cU
    @0
    @40
    cvv
    wcel
    #
    @89
    @40
    wceq
    @0
    c1o
    con0
    wcel
    @90
    1on
    cA
    c1o
    cV
    con0
    unexg
    mpan2
    @90
    @89
    c0
    @42
    cfv
    @40
    c0
    cF
    @42
    wunex2.f
    fveq1i
    @40
    cvv
    @39
    fr0g
    syl5eq
    syl
    @89
    @22
    cU
    cF
    c0
    fvssunirn
    wunex2.u
    sseqtr4i
    syl6eqssr
    #
    unssbd
    1n0
    c1o
    cU
    ssn0
    sylancl
    @0
    @13
    va
    cU
    @16
    @20
    @0
    @13
    @44
    @0
    @19
    @13
    vm
    com
    @46
    @6
    @8
    @12
    @46
    @8
    @6
    @46
    @7
    @5
    cpr
    #
    cU
    wss
    @8
    @6
    wa
    @46
    @92
    vv
    @18
    @4
    @55
    cpr
    #
    cmpt
    #
    crn
    #
    cU
    @46
    @92
    @95
    cun
    #
    @60
    cU
    @19
    @96
    @60
    wss
    @0
    @45
    vu
    @18
    @59
    @4
    @96
    vu
    va
    weq
    #
    @54
    @92
    @58
    @95
    @97
    @52
    @7
    @53
    @5
    @51
    @4
    pweq
    @51
    @4
    unieq
    preq12d
    #
    @97
    @57
    @94
    @97
    vv
    @18
    @56
    @93
    @51
    @4
    @55
    preq1
    #
    mpteq2dv
    rneqd
    uneq12d
    ssiun2s
    ad2antll
    @46
    @60
    @48
    cU
    @46
    @61
    @60
    @48
    @60
    @50
    ssun2
    @87
    syl5sseqr
    @88
    syl6ss
    sstrd
    unssad
    @7
    @5
    cU
    va
    vpwex
    va
    vuniex
    prss
    sylibr
    #
    simprd
    @46
    @8
    @6
    @100
    simpld
    @46
    @11
    vb
    cU
    @9
    cU
    wcel
    #
    @9
    vn
    cv
    #
    cF
    cfv
    #
    wcel
    #
    vn
    com
    wrex
    #
    @46
    @11
    @101
    @9
    @22
    wcel
    #
    @105
    cU
    @22
    @9
    wunex2.u
    eleq2i
    @24
    @106
    @105
    wb
    @43
    vn
    @9
    cF
    com
    fnunirn
    ax-mp
    bitri
    @46
    @104
    @11
    vn
    com
    @46
    @102
    com
    wcel
    #
    @104
    wa
    #
    wa
    #
    vv
    @17
    @102
    cun
    #
    cF
    cfv
    #
    @93
    cmpt
    #
    crn
    #
    cU
    @10
    @109
    @92
    @113
    cU
    @109
    @92
    @113
    cun
    #
    vu
    @111
    @54
    vv
    @111
    @56
    cmpt
    #
    crn
    #
    cun
    #
    ciun
    #
    cU
    @109
    @4
    @111
    wcel
    @114
    @118
    wss
    @109
    @18
    @111
    @4
    @109
    @110
    com
    wcel
    #
    @45
    @18
    @111
    wss
    #
    @109
    @45
    @107
    @119
    @0
    @45
    @19
    @108
    simplrl
    #
    @46
    @107
    @104
    simprl
    #
    com
    word
    @45
    @107
    @119
    ordom
    com
    @17
    @102
    ordunel
    mp3an1
    syl2anc
    #
    @121
    @119
    @45
    wa
    @17
    @110
    wss
    @120
    @17
    @102
    ssun1
    @18
    vk
    cv
    #
    cF
    cfv
    #
    wss
    #
    @18
    @18
    wss
    #
    @18
    vi
    cv
    #
    cF
    cfv
    #
    wss
    #
    @18
    @128
    csuc
    #
    cF
    cfv
    #
    wss
    #
    @120
    vk
    vi
    @110
    @17
    vk
    vm
    weq
    @125
    @18
    @18
    @124
    @17
    cF
    fveq2
    sseq2d
    #
    vk
    vi
    weq
    @125
    @129
    @18
    @124
    @128
    cF
    fveq2
    sseq2d
    #
    @124
    @131
    wceq
    @125
    @132
    @18
    @124
    @131
    cF
    fveq2
    sseq2d
    #
    @124
    @110
    wceq
    @125
    @111
    @18
    @124
    @110
    cF
    fveq2
    sseq2d
    @127
    @45
    @18
    ssid
    a1i
    #
    @128
    com
    wcel
    #
    @45
    wa
    #
    @17
    @128
    wss
    #
    wa
    #
    @129
    @132
    wss
    #
    @130
    @133
    @138
    @142
    @45
    @140
    @18
    @48
    wss
    @142
    vm
    @128
    com
    vm
    vi
    weq
    #
    @18
    @129
    @48
    @132
    @17
    @128
    cF
    fveq2
    @143
    @47
    @131
    cF
    @17
    @128
    suceq
    fveq2d
    sseq12d
    @45
    @61
    @18
    @48
    @18
    @50
    @61
    @18
    @49
    ssun1
    @62
    sstri
    @45
    @63
    @64
    @67
    @86
    mpan2
    syl5sseqr
    vtoclga
    ad2antrr
    @18
    @129
    @132
    sstr2
    syl5com
    #
    findsg
    mpan2
    syl2anc
    @0
    @45
    @19
    @108
    simplrr
    sseldd
    vu
    @111
    @117
    @4
    @114
    @97
    @54
    @92
    @116
    @113
    @98
    @97
    @115
    @112
    @97
    vv
    @111
    @56
    @93
    @99
    mpteq2dv
    rneqd
    uneq12d
    ssiun2s
    syl
    @109
    @118
    @110
    csuc
    #
    cF
    cfv
    #
    cU
    @109
    @111
    @111
    cuni
    #
    cun
    #
    @118
    cun
    #
    @118
    @146
    @118
    @148
    ssun2
    @109
    @119
    @149
    cvv
    wcel
    @146
    @149
    wceq
    @123
    @148
    @118
    @111
    @147
    @110
    cF
    fvex
    #
    @111
    @150
    uniex
    unex
    vu
    @111
    @117
    @150
    @54
    @116
    @66
    @115
    vv
    @111
    @56
    @150
    mptex
    rnex
    unex
    iunex
    unex
    vz
    vw
    @40
    @110
    @38
    @149
    @75
    cF
    cvv
    wunex2.f
    @83
    @68
    @111
    wceq
    #
    @70
    @148
    @74
    @118
    @151
    @68
    @111
    @69
    @147
    @151
    id
    #
    @68
    @111
    unieq
    uneq12d
    @151
    vu
    @68
    @111
    @73
    @117
    @152
    @151
    @72
    @116
    @54
    @151
    @71
    @115
    vv
    @68
    @111
    @56
    mpteq1
    rneqd
    uneq2d
    iuneq12d
    uneq12d
    frsucmpt2
    sylancl
    syl5sseqr
    @146
    @22
    cU
    cF
    @145
    fvssunirn
    wunex2.u
    sseqtr4i
    syl6ss
    sstrd
    unssbd
    @109
    @9
    @111
    wcel
    @10
    cvv
    wcel
    @10
    @113
    wcel
    @109
    @103
    @111
    @9
    @109
    @119
    @107
    @103
    @111
    wss
    #
    @123
    @122
    @107
    @102
    @128
    wss
    #
    wa
    #
    @103
    @129
    wss
    #
    wi
    @107
    @153
    wi
    vi
    @110
    com
    @128
    @110
    wceq
    #
    @155
    @107
    @156
    @153
    @157
    @107
    @155
    @157
    @154
    @107
    @157
    @110
    @102
    @128
    @102
    @17
    ssun2
    @157
    id
    syl5sseqr
    biantrud
    bicomd
    @157
    @129
    @111
    @103
    @128
    @110
    cF
    fveq2
    sseq2d
    imbi12d
    @138
    @107
    @154
    @156
    @141
    @130
    wi
    @138
    @107
    wa
    #
    @154
    wa
    #
    @156
    wi
    vm
    vn
    vm
    vn
    weq
    #
    @141
    @159
    @130
    @156
    @160
    @139
    @158
    @140
    @154
    @160
    @45
    @107
    @138
    @17
    @102
    com
    eleq1
    anbi2d
    @17
    @102
    @128
    sseq1
    anbi12d
    @160
    @18
    @103
    @129
    @17
    @102
    cF
    fveq2
    sseq1d
    imbi12d
    @126
    @127
    @130
    @133
    @130
    vk
    vi
    @128
    @17
    @134
    @135
    @136
    @135
    @137
    @144
    findsg
    chvarv
    expl
    vtoclga
    sylc
    @46
    @107
    @104
    simprr
    sseldd
    @4
    @9
    prex
    vv
    @111
    @93
    @10
    @9
    @112
    cvv
    @112
    eqid
    @55
    @9
    @4
    preq2
    elrnmpt1s
    sylancl
    sseldd
    rexlimdvaa
    syl5bi
    ralrimiv
    3jca
    rexlimdvaa
    syl5bi
    ralrimiv
    cU
    cvv
    wcel
    @1
    @2
    @3
    @14
    w3a
    wb
    cU
    @22
    cvv
    wunex2.u
    @21
    cF
    cF
    @42
    cvv
    wunex2.f
    @41
    wfun
    com
    cvv
    wcel
    @42
    cvv
    wcel
    @40
    @39
    rdgfun
    omex
    @41
    com
    cvv
    resfunexg
    mp2an
    eqeltri
    rnex
    uniex
    eqeltri
    va
    vb
    cU
    cvv
    iswun
    ax-mp
    syl3anbrc
    @0
    cA
    c1o
    cU
    @91
    unssad
    jca
end
