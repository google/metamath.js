include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cuni.mm"
include "cin.mm"
include "cmin.mm"
include "co.mm"
include "cpw.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "cint.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "wral.mm"
include "cc0.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "fveq2d.mm"
include "hash0.mm"
include "oveq2d.mm"
include "pweq.mm"
include "pw0.mm"
include "sumeq1d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "weq.mm"
include "uniun.mm"
include "vex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "mulid2d.mm"
include "cvv.mm"
include "cc.mm"
include "0ex.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "neg1cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "rint0.mm"
include "oveq12d.mm"
include "sumsn.mm"
include "sylancr.mm"
include "subid1d.mm"
include "3eqtr4rd.mm"
include "rgen.mm"
include "wn.mm"
include "wa.mm"
include "ineq1.mm"
include "simpl.mm"
include "ineq1d.mm"
include "sumeq2dv.mm"
include "rspcva.mm"
include "adantll.mm"
include "wss.mm"
include "simpr.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "in32.mm"
include "inass.mm"
include "sumeq2sdv.mm"
include "sylan.mm"
include "caddc.mm"
include "hashun3.mm"
include "syl2anc.mm"
include "indi.mm"
include "fveq2i.mm"
include "inindi.mm"
include "oveq2i.mm"
include "3eqtr4g.mm"
include "cn0.mm"
include "syl.mm"
include "addsubassd.mm"
include "eqtrd.mm"
include "adantl.mm"
include "subcld.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "cdif.mm"
include "disjdif.mm"
include "a1i.mm"
include "ssun1.mm"
include "sspwb.mm"
include "mpbi.mm"
include "undif.mm"
include "eqcomi.mm"
include "simpll.mm"
include "snfi.mm"
include "unfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "elpwi.mm"
include "syl2an.mm"
include "expcld.mm"
include "simplr.mm"
include "mulcld.mm"
include "fsumsplit.mm"
include "cmpt.mm"
include "inteq.mm"
include "intunsn.mm"
include "eqid.mm"
include "unss1.mm"
include "snex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "simpllr.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "ssel.mm"
include "syl2imc.mm"
include "mtod.mm"
include "eldifd.mm"
include "eldifi.mm"
include "elpwid.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "ssundif.mm"
include "elpw2.mm"
include "elpwunsn.mm"
include "ad2antll.mm"
include "snssd.mm"
include "ssequn2.mm"
include "eqcomd.mm"
include "uneq1.mm"
include "undif1.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "ad2antrl.mm"
include "ssneldd.mm"
include "difsnb.mm"
include "difeq1.mm"
include "difun2.mm"
include "impbid.mm"
include "f1o2d.mm"
include "fvmpt.mm"
include "sylan2.mm"
include "fsumf1o.mm"
include "cbvsumv.mm"
include "expp1d.mm"
include "wi.mm"
include "hashunsng.mm"
include "sseli.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"
include "mulm1d.mm"
include "oveq1d.mm"
include "mulneg1d.mm"
include "syl5eq.mm"
include "fsumneg.mm"
include "3eqtrd.mm"
include "sselda.mm"
include "syldan.mm"
include "fsumcl.mm"
include "negsubd.mm"
include "ex.mm"
include "ralrimdva.mm"
include "cbvralv.mm"
include "syl6ibr.mm"
include "findcard2s.mm"
include "rspccva.mm"

theorem incexclem
  let cA: class A
  let cB: class B
  let vs: setvar s
  let vb: setvar b
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A s
  disjoint B s
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B b
  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( ( # ` B ) - ( # ` ( B i^i U. A ) ) ) = sum_ s e. ~P A ( ( -u 1 ^ ( # ` s ) ) x. ( # ` ( B i^i |^| s ) ) ) )

  proof
    cA
    cfn
    wcel
    vb
    cv
    #
    chash
    cfv
    #
    @0
    cA
    cuni
    #
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    cA
    cpw
    #
    c1
    cneg
    #
    vs
    cv
    #
    chash
    cfv
    #
    cexp
    co
    #
    @0
    @8
    cint
    #
    cin
    #
    chash
    cfv
    #
    cmul
    co
    #
    vs
    csu
    #
    wceq
    #
    vb
    cfn
    wral
    #
    cB
    cfn
    wcel
    cB
    chash
    cfv
    #
    cB
    @2
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @6
    @10
    cB
    @11
    cin
    #
    chash
    cfv
    #
    cmul
    co
    #
    vs
    csu
    #
    wceq
    #
    @1
    @0
    vx
    cv
    #
    cuni
    #
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @27
    cpw
    #
    @14
    vs
    csu
    #
    wceq
    #
    vb
    cfn
    wral
    @1
    cc0
    cmin
    co
    #
    c0
    csn
    #
    @14
    vs
    csu
    #
    wceq
    #
    vb
    cfn
    wral
    @1
    @0
    vy
    cv
    #
    cuni
    #
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @39
    cpw
    #
    @14
    vs
    csu
    #
    wceq
    #
    vb
    cfn
    wral
    #
    @1
    @0
    @40
    vz
    cv
    #
    cun
    #
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @39
    @48
    csn
    #
    cun
    #
    cpw
    #
    @14
    vs
    csu
    #
    wceq
    #
    vb
    cfn
    wral
    #
    @17
    vx
    vy
    vz
    cA
    @27
    c0
    wceq
    #
    @34
    @38
    vb
    cfn
    @59
    @31
    @35
    @33
    @37
    @59
    @30
    cc0
    @1
    cmin
    @59
    @30
    c0
    chash
    cfv
    #
    cc0
    @59
    @29
    c0
    chash
    @59
    @29
    @0
    c0
    cin
    c0
    @59
    @28
    c0
    @0
    @59
    @28
    c0
    cuni
    c0
    @27
    c0
    unieq
    uni0
    syl6eq
    ineq2d
    @0
    in0
    syl6eq
    fveq2d
    hash0
    syl6eq
    oveq2d
    @59
    @32
    @36
    @14
    vs
    @59
    @32
    c0
    cpw
    @36
    @27
    c0
    pweq
    pw0
    syl6eq
    sumeq1d
    eqeq12d
    ralbidv
    vx
    vy
    weq
    #
    @34
    @46
    vb
    cfn
    @61
    @31
    @43
    @33
    @45
    @61
    @30
    @42
    @1
    cmin
    @61
    @29
    @41
    chash
    @61
    @28
    @40
    @0
    @27
    @39
    unieq
    ineq2d
    fveq2d
    oveq2d
    @61
    @32
    @44
    @14
    vs
    @27
    @39
    pweq
    sumeq1d
    eqeq12d
    ralbidv
    @27
    @54
    wceq
    #
    @34
    @57
    vb
    cfn
    @62
    @31
    @52
    @33
    @56
    @62
    @30
    @51
    @1
    cmin
    @62
    @29
    @50
    chash
    @62
    @28
    @49
    @0
    @62
    @28
    @54
    cuni
    #
    @49
    @27
    @54
    unieq
    @63
    @40
    @53
    cuni
    #
    cun
    @49
    @39
    @53
    uniun
    @64
    @48
    @40
    @48
    vz
    vex
    #
    unisn
    uneq2i
    eqtri
    syl6eq
    ineq2d
    fveq2d
    oveq2d
    @62
    @32
    @55
    @14
    vs
    @27
    @54
    pweq
    sumeq1d
    eqeq12d
    ralbidv
    @27
    cA
    wceq
    #
    @34
    @16
    vb
    cfn
    @66
    @31
    @5
    @33
    @15
    @66
    @30
    @4
    @1
    cmin
    @66
    @29
    @3
    chash
    @66
    @28
    @2
    @0
    @27
    cA
    unieq
    ineq2d
    fveq2d
    oveq2d
    @66
    @32
    @6
    @14
    vs
    @27
    cA
    pweq
    sumeq1d
    eqeq12d
    ralbidv
    @38
    vb
    cfn
    @0
    cfn
    wcel
    #
    c1
    @1
    cmul
    co
    #
    @1
    @37
    @35
    @67
    @1
    @67
    @1
    @0
    hashcl
    nn0cnd
    #
    mulid2d
    #
    @67
    c0
    cvv
    wcel
    @68
    cc
    wcel
    @37
    @68
    wceq
    0ex
    @67
    @68
    @1
    cc
    @70
    @69
    eqeltrd
    @14
    @68
    vs
    c0
    cvv
    @8
    c0
    wceq
    #
    @10
    c1
    @13
    @1
    cmul
    @71
    @10
    @7
    cc0
    cexp
    co
    #
    c1
    @71
    @9
    cc0
    @7
    cexp
    @71
    @9
    @60
    cc0
    @8
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq2d
    @7
    cc
    wcel
    #
    @72
    c1
    wceq
    neg1cn
    @7
    exp0
    ax-mp
    syl6eq
    @71
    @12
    @0
    chash
    @0
    @8
    rint0
    fveq2d
    oveq12d
    sumsn
    sylancr
    @67
    @1
    @69
    subid1d
    3eqtr4rd
    rgen
    @39
    cfn
    wcel
    #
    @48
    @39
    wcel
    #
    wn
    #
    wa
    #
    @47
    @27
    chash
    cfv
    #
    @27
    @49
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @55
    @10
    @27
    @11
    cin
    #
    chash
    cfv
    #
    cmul
    co
    #
    vs
    csu
    #
    wceq
    #
    vx
    cfn
    wral
    @58
    @77
    @47
    @86
    vx
    cfn
    @77
    @27
    cfn
    wcel
    #
    wa
    #
    @47
    @86
    @88
    @47
    wa
    #
    @78
    @27
    @40
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @27
    @48
    cin
    #
    chash
    cfv
    #
    @27
    @40
    @48
    cin
    #
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    cmin
    co
    #
    @44
    @84
    vs
    csu
    #
    @44
    @10
    @27
    @11
    @48
    cin
    #
    cin
    #
    chash
    cfv
    #
    cmul
    co
    #
    vs
    csu
    #
    cmin
    co
    #
    @81
    @85
    @89
    @92
    @100
    @98
    @105
    cmin
    @87
    @47
    @92
    @100
    wceq
    #
    @77
    @46
    @107
    vb
    @27
    cfn
    vb
    vx
    weq
    #
    @43
    @92
    @45
    @100
    @108
    @1
    @78
    @42
    @91
    cmin
    @0
    @27
    chash
    fveq2
    #
    @108
    @41
    @90
    chash
    @0
    @27
    @40
    ineq1
    fveq2d
    oveq12d
    @108
    @44
    @14
    @84
    vs
    @108
    @8
    @44
    wcel
    #
    wa
    #
    @13
    @83
    @10
    cmul
    @111
    @12
    @82
    chash
    @111
    @0
    @27
    @11
    @108
    @110
    simpl
    ineq1d
    fveq2d
    oveq2d
    sumeq2dv
    eqeq12d
    rspcva
    adantll
    @88
    @93
    cfn
    wcel
    #
    @47
    @98
    @105
    wceq
    #
    @88
    @87
    @93
    @27
    wss
    @112
    @77
    @87
    simpr
    #
    @27
    @48
    inss1
    @27
    @93
    ssfi
    sylancl
    #
    @46
    @113
    vb
    @93
    cfn
    @0
    @93
    wceq
    #
    @43
    @98
    @45
    @105
    @116
    @1
    @94
    @42
    @97
    cmin
    @0
    @93
    chash
    fveq2
    @116
    @41
    @96
    chash
    @116
    @41
    @93
    @40
    cin
    #
    @96
    @0
    @93
    @40
    ineq1
    @117
    @90
    @48
    cin
    @96
    @27
    @48
    @40
    in32
    @27
    @40
    @48
    inass
    eqtri
    syl6eq
    fveq2d
    oveq12d
    @116
    @44
    @14
    @104
    vs
    @116
    @13
    @103
    @10
    cmul
    @116
    @12
    @102
    chash
    @116
    @12
    @93
    @11
    cin
    #
    @102
    @0
    @93
    @11
    ineq1
    @118
    @82
    @48
    cin
    @102
    @27
    @48
    @11
    in32
    @27
    @11
    @48
    inass
    eqtri
    syl6eq
    fveq2d
    oveq2d
    sumeq2sdv
    eqeq12d
    rspcva
    sylan
    oveq12d
    @88
    @81
    @99
    wceq
    @47
    @88
    @81
    @78
    @91
    @98
    caddc
    co
    #
    cmin
    co
    @99
    @88
    @80
    @119
    @78
    cmin
    @88
    @80
    @91
    @94
    caddc
    co
    #
    @97
    cmin
    co
    #
    @119
    @88
    @90
    @93
    cun
    #
    chash
    cfv
    #
    @120
    @90
    @93
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    @80
    @121
    @88
    @90
    cfn
    wcel
    #
    @112
    @123
    @126
    wceq
    @88
    @87
    @90
    @27
    wss
    @127
    @114
    @27
    @40
    inss1
    @27
    @90
    ssfi
    sylancl
    #
    @115
    @90
    @93
    hashun3
    syl2anc
    @79
    @122
    chash
    @27
    @40
    @48
    indi
    fveq2i
    @97
    @125
    @120
    cmin
    @96
    @124
    chash
    @27
    @40
    @48
    inindi
    fveq2i
    oveq2i
    3eqtr4g
    @88
    @91
    @94
    @97
    @88
    @91
    @88
    @127
    @91
    cn0
    wcel
    @128
    @90
    hashcl
    syl
    nn0cnd
    #
    @88
    @94
    @88
    @112
    @94
    cn0
    wcel
    @115
    @93
    hashcl
    syl
    nn0cnd
    #
    @88
    @97
    @88
    @96
    cfn
    wcel
    #
    @97
    cn0
    wcel
    @88
    @87
    @96
    @27
    wss
    @131
    @114
    @27
    @95
    inss1
    @27
    @96
    ssfi
    sylancl
    @96
    hashcl
    syl
    nn0cnd
    #
    addsubassd
    eqtrd
    oveq2d
    @88
    @78
    @91
    @98
    @88
    @78
    @87
    @78
    cn0
    wcel
    @77
    @27
    hashcl
    adantl
    nn0cnd
    @129
    @88
    @94
    @97
    @130
    @132
    subcld
    subsub4d
    eqtr4d
    adantr
    @88
    @85
    @106
    wceq
    @47
    @88
    @85
    @100
    @55
    @44
    cdif
    #
    @84
    vs
    csu
    #
    caddc
    co
    @100
    @105
    cneg
    #
    caddc
    co
    @106
    @88
    @44
    @133
    @84
    @55
    vs
    @44
    @133
    cin
    c0
    wceq
    @88
    @44
    @55
    disjdif
    a1i
    @55
    @44
    @133
    cun
    #
    wceq
    @88
    @136
    @55
    @44
    @55
    wss
    #
    @136
    @55
    wceq
    @39
    @54
    wss
    @137
    @39
    @53
    ssun1
    @39
    @54
    sspwb
    mpbi
    #
    @44
    @55
    undif
    mpbi
    eqcomi
    a1i
    @88
    @54
    cfn
    wcel
    #
    @55
    cfn
    wcel
    @88
    @74
    @53
    cfn
    wcel
    @139
    @74
    @76
    @87
    simpll
    #
    @48
    snfi
    @39
    @53
    unfi
    sylancl
    #
    @54
    pwfi
    sylib
    @88
    @8
    @55
    wcel
    #
    wa
    #
    @10
    @83
    @143
    @7
    @9
    @73
    @143
    neg1cn
    a1i
    @143
    @8
    cfn
    wcel
    #
    @9
    cn0
    wcel
    #
    @88
    @139
    @8
    @54
    wss
    @144
    @142
    @141
    @8
    @54
    elpwi
    @54
    @8
    ssfi
    syl2an
    @8
    hashcl
    #
    syl
    expcld
    #
    @143
    @83
    @143
    @82
    cfn
    wcel
    #
    @83
    cn0
    wcel
    @143
    @87
    @82
    @27
    wss
    @148
    @77
    @87
    @142
    simplr
    #
    @27
    @11
    inss1
    @27
    @82
    ssfi
    sylancl
    @82
    hashcl
    syl
    nn0cnd
    mulcld
    #
    fsumsplit
    @88
    @134
    @135
    @100
    caddc
    @88
    @134
    @44
    @7
    vt
    cv
    #
    @53
    cun
    #
    chash
    cfv
    #
    cexp
    co
    #
    @27
    @151
    cint
    #
    @48
    cin
    #
    cin
    #
    chash
    cfv
    #
    cmul
    co
    #
    vt
    csu
    #
    @44
    @104
    cneg
    #
    vs
    csu
    #
    @135
    @88
    @133
    @84
    @44
    @159
    vs
    vt
    vu
    @44
    vu
    cv
    #
    @53
    cun
    #
    cmpt
    #
    @152
    @8
    @152
    wceq
    #
    @10
    @154
    @83
    @158
    cmul
    @166
    @9
    @153
    @7
    cexp
    @8
    @152
    chash
    fveq2
    oveq2d
    @166
    @82
    @157
    chash
    @166
    @11
    @156
    @27
    @166
    @11
    @152
    cint
    @156
    @8
    @152
    inteq
    @151
    @48
    @65
    intunsn
    syl6eq
    ineq2d
    fveq2d
    oveq12d
    @88
    @74
    @44
    cfn
    wcel
    @140
    @39
    pwfi
    sylib
    #
    @88
    vu
    vs
    @44
    @133
    @164
    @8
    @53
    cdif
    #
    @165
    @165
    eqid
    #
    @88
    @163
    @44
    wcel
    #
    wa
    #
    @164
    @55
    @44
    @171
    @164
    @54
    wss
    #
    @164
    @55
    wcel
    @171
    @163
    @39
    wss
    #
    @172
    @170
    @173
    @88
    @163
    @39
    elpwi
    #
    adantl
    @163
    @39
    @53
    unss1
    syl
    @164
    @54
    @163
    @53
    vu
    vex
    @48
    snex
    #
    unex
    elpw
    sylibr
    @171
    @164
    @44
    wcel
    #
    @75
    @74
    @76
    @87
    @170
    simpllr
    @176
    @164
    @39
    wss
    @171
    @48
    @164
    wcel
    #
    @75
    @164
    @39
    elpwi
    @177
    @171
    @177
    @53
    @164
    wss
    @53
    @163
    ssun2
    @48
    @164
    @65
    snss
    mpbir
    a1i
    @164
    @39
    @48
    ssel
    syl2imc
    mtod
    eldifd
    @88
    @8
    @133
    wcel
    #
    wa
    #
    @168
    @39
    wss
    #
    @168
    @44
    wcel
    @179
    @8
    @53
    @39
    cun
    #
    wss
    @180
    @179
    @8
    @54
    @181
    @179
    @8
    @54
    @178
    @142
    @88
    @8
    @55
    @44
    eldifi
    #
    adantl
    elpwid
    @39
    @53
    uncom
    syl6sseq
    @8
    @53
    @39
    ssundif
    sylib
    @168
    @39
    vy
    vex
    elpw2
    sylibr
    @88
    @170
    @178
    wa
    #
    wa
    #
    @163
    @168
    wceq
    #
    @8
    @164
    wceq
    #
    @184
    @186
    @185
    @8
    @8
    @53
    cun
    #
    wceq
    @184
    @187
    @8
    @184
    @53
    @8
    wss
    @187
    @8
    wceq
    @184
    @48
    @8
    @178
    @48
    @8
    wcel
    #
    @88
    @170
    @8
    @39
    @48
    elpwunsn
    ad2antll
    snssd
    @53
    @8
    ssequn2
    sylib
    eqcomd
    @185
    @164
    @187
    @8
    @185
    @164
    @168
    @53
    cun
    @187
    @163
    @168
    @53
    uneq1
    @8
    @53
    undif1
    syl6eq
    eqeq2d
    syl5ibrcom
    @184
    @185
    @186
    @163
    @163
    @53
    cdif
    #
    wceq
    @184
    @189
    @163
    @184
    @48
    @163
    wcel
    wn
    @189
    @163
    wceq
    @184
    @163
    @39
    @48
    @170
    @173
    @88
    @178
    @174
    ad2antrl
    @74
    @76
    @87
    @183
    simpllr
    ssneldd
    @48
    @163
    difsnb
    sylib
    eqcomd
    @186
    @168
    @189
    @163
    @186
    @168
    @164
    @53
    cdif
    @189
    @8
    @164
    @53
    difeq1
    @163
    @53
    difun2
    syl6eq
    eqeq2d
    syl5ibrcom
    impbid
    f1o2d
    @151
    @44
    wcel
    @151
    @165
    cfv
    @152
    wceq
    @88
    vu
    @151
    @164
    @152
    @44
    @165
    @163
    @151
    @53
    uneq1
    @169
    @151
    @53
    vt
    vex
    @175
    unex
    fvmpt
    adantl
    @178
    @88
    @142
    @84
    cc
    wcel
    #
    @182
    @150
    sylan2
    fsumf1o
    @88
    @160
    @44
    @7
    @187
    chash
    cfv
    #
    cexp
    co
    #
    @103
    cmul
    co
    #
    vs
    csu
    @162
    @44
    @159
    @193
    vt
    vs
    vt
    vs
    weq
    #
    @154
    @192
    @158
    @103
    cmul
    @194
    @153
    @191
    @7
    cexp
    @194
    @152
    @187
    chash
    @151
    @8
    @53
    uneq1
    fveq2d
    oveq2d
    @194
    @157
    @102
    chash
    @194
    @156
    @101
    @27
    @194
    @155
    @11
    @48
    @151
    @8
    inteq
    ineq1d
    ineq2d
    fveq2d
    oveq12d
    cbvsumv
    @88
    @44
    @193
    @161
    vs
    @88
    @110
    wa
    #
    @193
    @10
    cneg
    #
    @103
    cmul
    co
    @161
    @195
    @192
    @196
    @103
    cmul
    @195
    @192
    @7
    @10
    cmul
    co
    #
    @196
    @195
    @7
    @9
    c1
    caddc
    co
    #
    cexp
    co
    @10
    @7
    cmul
    co
    @192
    @197
    @195
    @7
    @9
    @73
    @195
    neg1cn
    a1i
    #
    @195
    @144
    @145
    @88
    @74
    @8
    @39
    wss
    #
    @144
    @110
    @140
    @8
    @39
    elpwi
    #
    @39
    @8
    ssfi
    syl2an
    #
    @146
    syl
    expp1d
    @195
    @191
    @198
    @7
    cexp
    @195
    @144
    @188
    wn
    #
    @191
    @198
    wceq
    #
    @202
    @195
    @8
    @39
    @48
    @110
    @200
    @88
    @201
    adantl
    @74
    @76
    @87
    @110
    simpllr
    ssneldd
    @48
    cvv
    wcel
    @144
    @203
    wa
    @204
    wi
    @65
    @8
    @48
    cvv
    hashunsng
    ax-mp
    syl2anc
    oveq2d
    @195
    @7
    @10
    @199
    @110
    @88
    @142
    @10
    cc
    wcel
    @44
    @55
    @8
    @138
    sseli
    #
    @147
    sylan2
    #
    mulcomd
    3eqtr4d
    @195
    @10
    @206
    mulm1d
    eqtrd
    oveq1d
    @195
    @10
    @103
    @206
    @110
    @88
    @142
    @103
    cc
    wcel
    @205
    @143
    @103
    @143
    @102
    cfn
    wcel
    #
    @103
    cn0
    wcel
    @143
    @87
    @102
    @27
    wss
    @207
    @149
    @27
    @101
    inss1
    @27
    @102
    ssfi
    sylancl
    @102
    hashcl
    syl
    nn0cnd
    #
    sylan2
    mulneg1d
    eqtrd
    sumeq2dv
    syl5eq
    @88
    @44
    @104
    vs
    @167
    @110
    @88
    @142
    @104
    cc
    wcel
    #
    @205
    @143
    @10
    @103
    @147
    @208
    mulcld
    #
    sylan2
    fsumneg
    3eqtrd
    oveq2d
    @88
    @100
    @105
    @88
    @44
    @84
    vs
    @167
    @88
    @110
    @142
    @190
    @88
    @44
    @55
    @8
    @137
    @88
    @138
    a1i
    sselda
    #
    @150
    syldan
    fsumcl
    @88
    @44
    @104
    vs
    @167
    @88
    @110
    @142
    @209
    @211
    @210
    syldan
    fsumcl
    negsubd
    3eqtrd
    adantr
    3eqtr4d
    ex
    ralrimdva
    @57
    @86
    vb
    vx
    cfn
    @108
    @52
    @81
    @56
    @85
    @108
    @1
    @78
    @51
    @80
    cmin
    @109
    @108
    @50
    @79
    chash
    @0
    @27
    @49
    ineq1
    fveq2d
    oveq12d
    @108
    @55
    @14
    @84
    vs
    @108
    @13
    @83
    @10
    cmul
    @108
    @12
    @82
    chash
    @0
    @27
    @11
    ineq1
    fveq2d
    oveq2d
    sumeq2sdv
    eqeq12d
    cbvralv
    syl6ibr
    findcard2s
    @16
    @26
    vb
    cB
    cfn
    @0
    cB
    wceq
    #
    @5
    @21
    @15
    @25
    @212
    @1
    @18
    @4
    @20
    cmin
    @0
    cB
    chash
    fveq2
    @212
    @3
    @19
    chash
    @0
    cB
    @2
    ineq1
    fveq2d
    oveq12d
    @212
    @6
    @14
    @24
    vs
    @212
    @8
    @6
    wcel
    #
    wa
    #
    @13
    @23
    @10
    cmul
    @214
    @12
    @22
    chash
    @214
    @0
    cB
    @11
    @212
    @213
    simpl
    ineq1d
    fveq2d
    oveq2d
    sumeq2dv
    eqeq12d
    rspccva
    sylan
end
