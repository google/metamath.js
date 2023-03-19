include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "cc0.mm"
include "cicc.mm"
include "wrex.mm"
include "cle.mm"
include "wb.mm"
include "wo.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "ad2antrl.mm"
include "simpll2.mm"
include "ad2antll.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "cpnf.mm"
include "cico.mm"
include "axcontlem6.mm"
include "anim12dan.mm"
include "an4.mm"
include "r19.26.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "id.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeqan12d.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "rexbidv.mm"
include "cc.mm"
include "fveecn.mm"
include "sylan.mm"
include "simpll3.mm"
include "cr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recnd.mm"
include "adantr.mm"
include "elrege0.mm"
include "simplbi.mm"
include "adantl.mm"
include "ax-1cn.mm"
include "simpr1.mm"
include "simpr3.mm"
include "mulcld.mm"
include "subcl.mm"
include "sylancr.mm"
include "mpan.mm"
include "3ad2ant2.mm"
include "simpll.mm"
include "subdird.mm"
include "simpr2.mm"
include "nnncan1.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "subdi.mm"
include "mp3an2.mm"
include "mulid1.mm"
include "eqtrd.mm"
include "npncan.mm"
include "eqtr2d.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "adddird.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"
include "simplr.mm"
include "eqeq12d.mm"
include "addcld.mm"
include "addsubeq4d.mm"
include "addassd.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "3bitr2rd.mm"
include "syl23anc.mm"
include "ralbidva.mm"
include "subcld.mm"
include "mulcan1g.mm"
include "r19.32v.mm"
include "wn.mm"
include "neneqd.mm"
include "biorf.mm"
include "orcom.mm"
include "syl6bb.mm"
include "subeq0ad.mm"
include "eqeefv.mm"
include "3adant1.mm"
include "orbi2d.mm"
include "3bitr3rd.mm"
include "syl5bb.mm"
include "3bitrd.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "1red.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "simp3bi.mm"
include "lemul1a.mm"
include "syl31anc.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "wi.mm"
include "0elunit.mm"
include "simpl.mm"
include "mul02d.mm"
include "oveq1.mm"
include "rspcev.mm"
include "adantrl.mm"
include "a1d.mm"
include "ex.mm"
include "cdiv.mm"
include "simp3.mm"
include "clt.mm"
include "simprbi.mm"
include "0red.mm"
include "simp1.mm"
include "ne0gt0d.mm"
include "ltletrd.mm"
include "divelunit.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "gt0ne0d.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "3exp.mm"
include "pm2.61ine.mm"
include "impbid.mm"
include "bitrd.mm"
include "sylan9bbr.mm"
include "anasss.mm"
include "sylan2b.mm"
include "syldan.mm"

theorem axcontlem7
  let vx: setvar x
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let vi: setvar i
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  assume axcontlem7.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }
  assume axcontlem7.2: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint D t
  disjoint t x
  disjoint D x
  disjoint F i
  disjoint i t
  disjoint F t
  disjoint i p
  disjoint i x
  disjoint N i
  disjoint p t
  disjoint p x
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint P i
  disjoint P t
  disjoint P x
  disjoint Q i
  disjoint Q t
  disjoint Q x
  disjoint U i
  disjoint U p
  disjoint U t
  disjoint U x
  disjoint Z i
  disjoint Z p
  disjoint Z t
  disjoint Z x
  assert |- ( ( ( ( N e. NN /\ Z e. ( EE ` N ) /\ U e. ( EE ` N ) ) /\ Z =/= U ) /\ ( P e. D /\ Q e. D ) ) -> ( P Btwn <. Z , Q >. <-> ( F ` P ) <_ ( F ` Q ) ) )

  proof
    cN
    cn
    wcel
    #
    cZ
    cN
    cee
    cfv
    #
    wcel
    #
    cU
    @1
    wcel
    #
    w3a
    #
    cZ
    cU
    wne
    #
    wa
    #
    cP
    cD
    wcel
    #
    cQ
    cD
    wcel
    #
    wa
    #
    wa
    #
    cP
    cZ
    cQ
    cop
    cbtwn
    wbr
    #
    vi
    cv
    #
    cP
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @12
    cZ
    cfv
    #
    cmul
    co
    #
    @14
    @12
    cQ
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    vt
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    #
    cle
    wbr
    #
    @10
    cP
    @1
    wcel
    #
    @2
    cQ
    @1
    wcel
    #
    @11
    @25
    wb
    @7
    @29
    @6
    @8
    cD
    @1
    cP
    cD
    cU
    cZ
    vp
    cv
    #
    cop
    cbtwn
    wbr
    @31
    cZ
    cU
    cop
    cbtwn
    wbr
    wo
    #
    vp
    @1
    crab
    @1
    axcontlem7.1
    @32
    vp
    @1
    ssrab2
    eqsstri
    #
    sseli
    ad2antrl
    @0
    @2
    @3
    @5
    @9
    simpll2
    @8
    @30
    @6
    @7
    cD
    @1
    cQ
    @33
    sseli
    ad2antll
    vt
    cP
    cZ
    cQ
    vi
    cN
    brbtwn
    syl3anc
    @6
    @9
    @26
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @13
    c1
    @26
    cmin
    co
    #
    @16
    cmul
    co
    #
    @26
    @12
    cU
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @22
    wral
    #
    wa
    #
    @27
    @34
    wcel
    #
    @18
    c1
    @27
    cmin
    co
    #
    @16
    cmul
    co
    #
    @27
    @38
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @22
    wral
    #
    wa
    #
    wa
    #
    @25
    @28
    wb
    #
    @6
    @7
    @43
    @8
    @51
    vx
    vt
    cD
    cP
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem7.1
    axcontlem7.2
    axcontlem6
    vx
    vt
    cD
    cQ
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem7.1
    axcontlem7.2
    axcontlem6
    anim12dan
    @52
    @6
    @35
    @44
    wa
    #
    @41
    @49
    wa
    #
    vi
    @22
    wral
    #
    wa
    #
    @53
    @52
    @54
    @42
    @50
    wa
    #
    wa
    @57
    @35
    @42
    @44
    @50
    an4
    @56
    @58
    @54
    @41
    @49
    vi
    @22
    r19.26
    anbi2i
    bitr4i
    @6
    @54
    @56
    @53
    @56
    @25
    @40
    @17
    @14
    @48
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @22
    wral
    #
    vt
    @24
    wrex
    #
    @6
    @54
    wa
    #
    @28
    @56
    @23
    @62
    vt
    @24
    @56
    @21
    @61
    wb
    #
    vi
    @22
    wral
    @23
    @62
    wb
    @55
    @65
    vi
    @22
    @41
    @49
    @13
    @40
    @20
    @60
    @41
    id
    @49
    @19
    @59
    @17
    caddc
    @18
    @48
    @14
    cmul
    oveq2
    oveq2d
    eqeqan12d
    ralimi
    @21
    @61
    vi
    @22
    ralbi
    syl
    rexbidv
    @64
    @63
    @26
    @14
    @27
    cmul
    co
    #
    wceq
    #
    vt
    @24
    wrex
    #
    @28
    @64
    @62
    @67
    vt
    @24
    @6
    @54
    @14
    @24
    wcel
    #
    @62
    @67
    wb
    @6
    @54
    @69
    wa
    #
    wa
    #
    @62
    @26
    @66
    cmin
    co
    #
    @16
    cmul
    co
    #
    @72
    @38
    cmul
    co
    #
    wceq
    #
    vi
    @22
    wral
    @72
    cc0
    wceq
    #
    @16
    @38
    wceq
    #
    wo
    #
    vi
    @22
    wral
    #
    @67
    @71
    @61
    @75
    vi
    @22
    @71
    @12
    @22
    wcel
    #
    wa
    #
    @16
    cc
    wcel
    #
    @38
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    @26
    cc
    wcel
    #
    @27
    cc
    wcel
    #
    @61
    @75
    wb
    @71
    @2
    @80
    @82
    @0
    @2
    @3
    @5
    @70
    simpll2
    cZ
    @12
    cN
    fveecn
    sylan
    #
    @71
    @3
    @80
    @83
    @0
    @2
    @3
    @5
    @70
    simpll3
    cU
    @12
    cN
    fveecn
    sylan
    #
    @71
    @84
    @80
    @69
    @84
    @6
    @54
    @69
    @14
    @69
    @14
    cr
    wcel
    #
    cc0
    @14
    cle
    wbr
    #
    @14
    c1
    cle
    wbr
    #
    cc0
    c1
    @14
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    recnd
    ad2antll
    #
    adantr
    #
    @71
    @85
    @80
    @54
    @85
    @6
    @69
    @35
    @85
    @44
    @35
    @26
    @35
    @26
    cr
    wcel
    #
    cc0
    @26
    cle
    wbr
    #
    @26
    elrege0
    #
    simplbi
    #
    recnd
    adantr
    #
    ad2antrl
    #
    adantr
    #
    @71
    @86
    @80
    @54
    @86
    @6
    @69
    @44
    @86
    @35
    @44
    @27
    @44
    @27
    cr
    wcel
    #
    cc0
    @27
    cle
    wbr
    #
    @27
    elrege0
    #
    simplbi
    #
    recnd
    #
    adantl
    #
    ad2antrl
    #
    adantr
    #
    @82
    @83
    wa
    #
    @84
    @85
    @86
    w3a
    #
    wa
    #
    @75
    @17
    @14
    @46
    cmul
    co
    #
    caddc
    co
    #
    @37
    cmin
    co
    #
    @39
    @14
    @47
    cmul
    co
    #
    cmin
    co
    #
    wceq
    @40
    @115
    @117
    caddc
    co
    #
    wceq
    @61
    @113
    @73
    @116
    @74
    @118
    @113
    c1
    @66
    cmin
    co
    #
    @36
    cmin
    co
    #
    @16
    cmul
    co
    @120
    @16
    cmul
    co
    #
    @37
    cmin
    co
    @73
    @116
    @113
    @120
    @36
    @16
    @113
    c1
    cc
    wcel
    #
    @66
    cc
    wcel
    #
    @120
    cc
    wcel
    ax-1cn
    @113
    @14
    @27
    @111
    @84
    @85
    @86
    simpr1
    #
    @111
    @84
    @85
    @86
    simpr3
    #
    mulcld
    #
    c1
    @66
    subcl
    sylancr
    @112
    @36
    cc
    wcel
    #
    @111
    @85
    @84
    @128
    @86
    @123
    @85
    @128
    ax-1cn
    c1
    @26
    subcl
    mpan
    3ad2ant2
    adantl
    #
    @82
    @83
    @112
    simpll
    #
    subdird
    @113
    @121
    @72
    @16
    cmul
    @113
    @124
    @85
    @121
    @72
    wceq
    #
    @127
    @111
    @84
    @85
    @86
    simpr2
    #
    @123
    @124
    @85
    @131
    ax-1cn
    c1
    @66
    @26
    nnncan1
    mp3an1
    syl2anc
    oveq1d
    @113
    @122
    @115
    @37
    cmin
    @113
    @122
    @15
    @14
    @45
    cmul
    co
    #
    caddc
    co
    #
    @16
    cmul
    co
    @17
    @133
    @16
    cmul
    co
    #
    caddc
    co
    @115
    @113
    @120
    @134
    @16
    cmul
    @113
    @134
    @15
    @14
    @66
    cmin
    co
    #
    caddc
    co
    #
    @120
    @113
    @133
    @136
    @15
    caddc
    @113
    @84
    @86
    @133
    @136
    wceq
    @125
    @126
    @84
    @86
    wa
    #
    @133
    @14
    c1
    cmul
    co
    #
    @66
    cmin
    co
    #
    @136
    @84
    @123
    @86
    @133
    @140
    wceq
    ax-1cn
    @14
    c1
    @27
    subdi
    mp3an2
    @138
    @139
    @14
    @66
    cmin
    @84
    @139
    @14
    wceq
    @86
    @14
    mulid1
    adantr
    oveq1d
    eqtrd
    syl2anc
    oveq2d
    @113
    @84
    @124
    @137
    @120
    wceq
    #
    @125
    @127
    @123
    @84
    @124
    @141
    ax-1cn
    c1
    @14
    @66
    npncan
    mp3an1
    syl2anc
    eqtr2d
    oveq1d
    @113
    @15
    @133
    @16
    @112
    @15
    cc
    wcel
    #
    @111
    @84
    @85
    @142
    @86
    @123
    @84
    @142
    ax-1cn
    c1
    @14
    subcl
    mpan
    3ad2ant1
    adantl
    #
    @113
    @14
    @45
    @125
    @112
    @45
    cc
    wcel
    #
    @111
    @86
    @84
    @144
    @85
    @123
    @86
    @144
    ax-1cn
    c1
    @27
    subcl
    mpan
    3ad2ant3
    adantl
    #
    mulcld
    @130
    adddird
    @113
    @135
    @114
    @17
    caddc
    @113
    @14
    @45
    @16
    @125
    @145
    @130
    mulassd
    oveq2d
    3eqtrd
    oveq1d
    3eqtr3d
    @113
    @74
    @39
    @66
    @38
    cmul
    co
    #
    cmin
    co
    @118
    @113
    @26
    @66
    @38
    @132
    @127
    @82
    @83
    @112
    simplr
    #
    subdird
    @113
    @146
    @117
    @39
    cmin
    @113
    @14
    @27
    @38
    @125
    @126
    @147
    mulassd
    oveq2d
    eqtrd
    eqeq12d
    @113
    @37
    @39
    @115
    @117
    @113
    @36
    @16
    @129
    @130
    mulcld
    @113
    @26
    @38
    @132
    @147
    mulcld
    @113
    @17
    @114
    @113
    @15
    @16
    @143
    @130
    mulcld
    #
    @113
    @14
    @46
    @125
    @113
    @45
    @16
    @145
    @130
    mulcld
    #
    mulcld
    #
    addcld
    @113
    @14
    @47
    @125
    @113
    @27
    @38
    @126
    @147
    mulcld
    #
    mulcld
    #
    addsubeq4d
    @113
    @119
    @60
    @40
    @113
    @119
    @17
    @114
    @117
    caddc
    co
    #
    caddc
    co
    @60
    @113
    @17
    @114
    @117
    @148
    @150
    @152
    addassd
    @113
    @59
    @153
    @17
    caddc
    @113
    @14
    @46
    @47
    @125
    @149
    @151
    adddid
    oveq2d
    eqtr4d
    eqeq2d
    3bitr2rd
    syl23anc
    ralbidva
    @71
    @75
    @78
    vi
    @22
    @81
    @72
    cc
    wcel
    @82
    @83
    @75
    @78
    wb
    @81
    @26
    @66
    @102
    @81
    @14
    @27
    @95
    @110
    mulcld
    subcld
    @87
    @88
    @72
    @16
    @38
    mulcan1g
    syl3anc
    ralbidva
    @79
    @76
    @77
    vi
    @22
    wral
    #
    wo
    #
    @71
    @67
    @76
    @77
    vi
    @22
    r19.32v
    @71
    @76
    @76
    cZ
    cU
    wceq
    #
    wo
    #
    @67
    @155
    @71
    @156
    wn
    #
    @76
    @157
    wb
    @71
    cZ
    cU
    @4
    @5
    @70
    simplr
    neneqd
    @158
    @76
    @156
    @76
    wo
    @157
    @156
    @76
    biorf
    @156
    @76
    orcom
    syl6bb
    syl
    @71
    @26
    @66
    @101
    @71
    @14
    @27
    @94
    @109
    mulcld
    subeq0ad
    @71
    @156
    @154
    @76
    @6
    @156
    @154
    wb
    #
    @70
    @4
    @159
    @5
    @2
    @3
    @159
    @0
    cZ
    cU
    vi
    cN
    eqeefv
    3adant1
    adantr
    adantr
    orbi2d
    3bitr3rd
    syl5bb
    3bitrd
    anassrs
    rexbidva
    @54
    @68
    @28
    wb
    @6
    @54
    @68
    @28
    @54
    @67
    @28
    vt
    @24
    @70
    @28
    @67
    @66
    @27
    cle
    wbr
    @70
    @66
    c1
    @27
    cmul
    co
    #
    @27
    cle
    @70
    @89
    c1
    cr
    wcel
    @103
    @104
    wa
    #
    @91
    @66
    @160
    cle
    wbr
    @69
    @89
    @54
    @93
    adantl
    @70
    1red
    @44
    @161
    @35
    @69
    @44
    @161
    @105
    biimpi
    ad2antlr
    @69
    @91
    @54
    @69
    @89
    @90
    @91
    @92
    simp3bi
    adantl
    @14
    c1
    @27
    lemul1a
    syl31anc
    @70
    @27
    @44
    @86
    @35
    @69
    @107
    ad2antlr
    mulid2d
    breqtrd
    @26
    @66
    @27
    cle
    breq1
    syl5ibrcom
    rexlimdva
    @54
    @28
    @68
    wi
    #
    wi
    @26
    cc0
    @26
    cc0
    wceq
    #
    @54
    @162
    @163
    @54
    wa
    @68
    @28
    @163
    @44
    @68
    @35
    @163
    @44
    wa
    #
    cc0
    @24
    wcel
    @26
    cc0
    @27
    cmul
    co
    #
    wceq
    #
    @68
    0elunit
    @164
    @26
    cc0
    @165
    @163
    @44
    simpl
    @44
    @165
    cc0
    wceq
    @163
    @44
    @27
    @107
    mul02d
    adantl
    eqtr4d
    @67
    @166
    vt
    cc0
    @24
    @14
    cc0
    wceq
    @66
    @165
    @26
    @14
    cc0
    @27
    cmul
    oveq1
    eqeq2d
    rspcev
    sylancr
    adantrl
    a1d
    ex
    @26
    cc0
    wne
    #
    @54
    @28
    @68
    @167
    @54
    @28
    w3a
    #
    @26
    @27
    cdiv
    co
    #
    @24
    wcel
    #
    @26
    @169
    @27
    cmul
    co
    #
    wceq
    #
    @68
    @168
    @170
    @28
    @167
    @54
    @28
    simp3
    #
    @168
    @96
    @97
    @103
    cc0
    @27
    clt
    wbr
    @170
    @28
    wb
    @54
    @167
    @96
    @28
    @35
    @96
    @44
    @99
    adantr
    3ad2ant2
    #
    @54
    @167
    @97
    @28
    @35
    @97
    @44
    @35
    @96
    @97
    @98
    simprbi
    adantr
    3ad2ant2
    #
    @54
    @167
    @103
    @28
    @44
    @103
    @35
    @106
    adantl
    3ad2ant2
    #
    @168
    cc0
    @26
    @27
    @168
    0red
    @174
    @176
    @168
    @26
    @174
    @175
    @167
    @54
    @28
    simp1
    ne0gt0d
    @173
    ltletrd
    #
    @26
    @27
    divelunit
    syl22anc
    mpbird
    @168
    @171
    @26
    @168
    @26
    @27
    @54
    @167
    @85
    @28
    @100
    3ad2ant2
    @54
    @167
    @86
    @28
    @108
    3ad2ant2
    @168
    @27
    @177
    gt0ne0d
    divcan1d
    eqcomd
    @67
    @172
    vt
    @169
    @24
    @14
    @169
    wceq
    @66
    @171
    @26
    @14
    @169
    @27
    cmul
    oveq1
    eqeq2d
    rspcev
    syl2anc
    3exp
    pm2.61ine
    impbid
    adantl
    bitrd
    sylan9bbr
    anasss
    sylan2b
    syldan
    bitrd
end
