include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cprod.mm"
include "crepr.mm"
include "wceq.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wss.mm"
include "nn0ssre.mm"
include "a1i.mm"
include "sselda.mm"
include "leid.mm"
include "syl.mm"
include "wi.mm"
include "caddc.mm"
include "breq1.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "csn.mm"
include "c0.mm"
include "cc.mm"
include "0nn0.mm"
include "cfn.mm"
include "cif.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "0zd.mm"
include "repr0.mm"
include "eqid.mm"
include "iftruei.mm"
include "syl6eq.mm"
include "snfi.mm"
include "syl6eqel.mm"
include "fzo0.mm"
include "prodeq1i.mm"
include "prod0.mm"
include "eqtri.mm"
include "exp0.mm"
include "oveq12d.mm"
include "ax-1cn.mm"
include "mulid1i.mm"
include "fsumcl.mm"
include "simpl.mm"
include "sumsn.mm"
include "sylancr.mm"
include "sumeq1d.mm"
include "cvv.mm"
include "0ex.mm"
include "mulcld.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "ralrimivw.mm"
include "prodeq2d.mm"
include "3eqtr2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "fz0sn.mm"
include "3eqtr4rd.mm"
include "a1d.mm"
include "simpll.mm"
include "simplr.mm"
include "cbvsumv.mm"
include "eqeq2i.mm"
include "fveq1d.mm"
include "sumeq2dv.mm"
include "cbvprodv.mm"
include "prodeq2i.mm"
include "fveq12d.mm"
include "oveq1i.mm"
include "sumeq2i.mm"
include "prodeq2dv.mm"
include "eqeq12i.mm"
include "bitri.mm"
include "imbi2i.mm"
include "sylib.mm"
include "simpr.mm"
include "ad3antrrr.mm"
include "cmap.mm"
include "wf.mm"
include "simpllr.mm"
include "sseldi.mm"
include "1red.mm"
include "readdcld.mm"
include "ltp1d.mm"
include "ltled.mm"
include "letrd.mm"
include "sylibr.mm"
include "mpd.mm"
include "breprexplemc.mm"
include "syl21anc.mm"
include "ex.mm"
include "nn0indd.mm"
include "mpdan.mm"

theorem breprexp
  let wph: wff ph
  let cS: class S
  let vm: setvar m
  let cL: class L
  let cN: class N
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vs: setvar s
  let vt: setvar t
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  assume breprexp.n: |- ( ph -> N e. NN0 )
  assume breprexp.s: |- ( ph -> S e. NN0 )
  assume breprexp.z: |- ( ph -> Z e. CC )
  assume breprexp.h: |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) )

  disjoint L c
  disjoint L m
  disjoint c m
  disjoint L a
  disjoint L b
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint S b
  disjoint Z a
  disjoint Z b
  disjoint Z c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint m ph
  disjoint a m
  disjoint b m
  disjoint N c
  disjoint N m
  disjoint c m
  disjoint S a
  disjoint S c
  disjoint S m
  disjoint a c
  disjoint a m
  disjoint Z c
  disjoint Z m
  disjoint b c
  disjoint c ph
  disjoint L s
  disjoint L t
  disjoint c s
  disjoint c t
  disjoint m s
  disjoint m t
  disjoint s t
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N n
  disjoint Z i
  disjoint Z j
  disjoint Z k
  disjoint Z n
  disjoint a s
  disjoint b s
  disjoint i m
  disjoint i s
  disjoint j m
  disjoint j s
  disjoint k m
  disjoint k s
  disjoint m n
  disjoint n s
  disjoint N s
  disjoint N t
  disjoint c s
  disjoint c t
  disjoint m s
  disjoint m t
  disjoint s t
  disjoint S s
  disjoint S t
  disjoint a s
  disjoint a t
  disjoint Z s
  disjoint Z t
  disjoint b s
  disjoint b t
  disjoint ph s
  disjoint ph t
  assert |- ( ph -> prod_ a e. ( 0 ..^ S ) sum_ b e. ( 1 ... N ) ( ( ( L ` a ) ` b ) x. ( Z ^ b ) ) = sum_ m e. ( 0 ... ( S x. N ) ) sum_ c e. ( ( 1 ... N ) ( repr ` S ) m ) ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) ) x. ( Z ^ m ) ) )

  proof
    wph
    cS
    cn0
    wcel
    #
    cc0
    cS
    cfzo
    co
    #
    c1
    cN
    cfz
    co
    #
    vb
    cv
    #
    va
    cv
    #
    cL
    cfv
    #
    cfv
    #
    cZ
    @3
    cexp
    co
    #
    cmul
    co
    #
    vb
    csu
    #
    va
    cprod
    #
    cc0
    cS
    cN
    cmul
    co
    #
    cfz
    co
    #
    @2
    vm
    cv
    #
    cS
    crepr
    cfv
    #
    co
    #
    @1
    @4
    vc
    cv
    #
    cfv
    #
    @5
    cfv
    #
    va
    cprod
    #
    cZ
    @13
    cexp
    co
    #
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    wceq
    #
    breprexp.s
    wph
    @0
    wa
    #
    cS
    cS
    cle
    wbr
    #
    @24
    @25
    cS
    cr
    wcel
    @26
    wph
    cn0
    cr
    cS
    cn0
    cr
    wss
    wph
    nn0ssre
    a1i
    sselda
    cS
    leid
    syl
    wph
    vt
    cv
    #
    cS
    cle
    wbr
    #
    cc0
    @27
    cfzo
    co
    #
    @9
    va
    cprod
    #
    cc0
    @27
    cN
    cmul
    co
    #
    cfz
    co
    #
    @2
    @13
    @27
    crepr
    cfv
    #
    co
    #
    @29
    @18
    va
    cprod
    #
    @20
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    wceq
    #
    wi
    cc0
    cS
    cle
    wbr
    #
    cc0
    cc0
    cfzo
    co
    #
    @9
    va
    cprod
    #
    cc0
    cc0
    cN
    cmul
    co
    #
    cfz
    co
    #
    @2
    @13
    cc0
    crepr
    cfv
    #
    co
    #
    @41
    @18
    va
    cprod
    #
    @20
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    wceq
    #
    wi
    vs
    cv
    #
    cS
    cle
    wbr
    #
    cc0
    @52
    cfzo
    co
    #
    @9
    va
    cprod
    #
    cc0
    @52
    cN
    cmul
    co
    #
    cfz
    co
    #
    @2
    @13
    @52
    crepr
    cfv
    #
    co
    #
    @54
    @18
    va
    cprod
    #
    @20
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    wceq
    #
    wi
    #
    @52
    c1
    caddc
    co
    #
    cS
    cle
    wbr
    #
    cc0
    @66
    cfzo
    co
    #
    @9
    va
    cprod
    #
    cc0
    @66
    cN
    cmul
    co
    #
    cfz
    co
    #
    @2
    @13
    @66
    crepr
    cfv
    #
    co
    #
    @68
    @18
    va
    cprod
    #
    @20
    cmul
    co
    #
    vc
    csu
    #
    vm
    csu
    #
    wceq
    #
    wi
    @26
    @24
    wi
    vt
    vs
    cS
    @27
    cc0
    wceq
    #
    @28
    @40
    @39
    @51
    @27
    cc0
    cS
    cle
    breq1
    @79
    @30
    @42
    @38
    @50
    @79
    @29
    @41
    @9
    va
    @27
    cc0
    cc0
    cfzo
    oveq2
    #
    prodeq1d
    @79
    @32
    @44
    @37
    @49
    vm
    @79
    @31
    @43
    cc0
    cfz
    @27
    cc0
    cN
    cmul
    oveq1
    oveq2d
    @79
    @37
    @49
    wceq
    @13
    @32
    wcel
    #
    @79
    @34
    @46
    @36
    @48
    vc
    @79
    @33
    @45
    @2
    @13
    @27
    cc0
    crepr
    fveq2
    oveqd
    @79
    @36
    @48
    wceq
    @16
    @34
    wcel
    #
    @79
    @35
    @47
    @20
    cmul
    @79
    @29
    @41
    @18
    va
    @80
    prodeq1d
    oveq1d
    adantr
    sumeq12dv
    adantr
    sumeq12dv
    eqeq12d
    imbi12d
    @27
    @52
    wceq
    #
    @28
    @53
    @39
    @64
    @27
    @52
    cS
    cle
    breq1
    @83
    @30
    @55
    @38
    @63
    @83
    @29
    @54
    @9
    va
    @27
    @52
    cc0
    cfzo
    oveq2
    #
    prodeq1d
    @83
    @32
    @57
    @37
    @62
    vm
    @83
    @31
    @56
    cc0
    cfz
    @27
    @52
    cN
    cmul
    oveq1
    oveq2d
    @83
    @37
    @62
    wceq
    @81
    @83
    @34
    @59
    @36
    @61
    vc
    @83
    @33
    @58
    @2
    @13
    @27
    @52
    crepr
    fveq2
    oveqd
    @83
    @36
    @61
    wceq
    @82
    @83
    @35
    @60
    @20
    cmul
    @83
    @29
    @54
    @18
    va
    @84
    prodeq1d
    oveq1d
    adantr
    sumeq12dv
    adantr
    sumeq12dv
    eqeq12d
    imbi12d
    @27
    @66
    wceq
    #
    @28
    @67
    @39
    @78
    @27
    @66
    cS
    cle
    breq1
    @85
    @30
    @69
    @38
    @77
    @85
    @29
    @68
    @9
    va
    @27
    @66
    cc0
    cfzo
    oveq2
    #
    prodeq1d
    @85
    @32
    @71
    @37
    @76
    vm
    @85
    @31
    @70
    cc0
    cfz
    @27
    @66
    cN
    cmul
    oveq1
    oveq2d
    @85
    @37
    @76
    wceq
    @81
    @85
    @34
    @73
    @36
    @75
    vc
    @85
    @33
    @72
    @2
    @13
    @27
    @66
    crepr
    fveq2
    oveqd
    @85
    @36
    @75
    wceq
    @82
    @85
    @35
    @74
    @20
    cmul
    @85
    @29
    @68
    @18
    va
    @86
    prodeq1d
    oveq1d
    adantr
    sumeq12dv
    adantr
    sumeq12dv
    eqeq12d
    imbi12d
    @27
    cS
    wceq
    #
    @28
    @26
    @39
    @24
    @27
    cS
    cS
    cle
    breq1
    @87
    @30
    @10
    @38
    @23
    @87
    @29
    @1
    @9
    va
    @27
    cS
    cc0
    cfzo
    oveq2
    #
    prodeq1d
    @87
    @32
    @12
    @37
    @22
    vm
    @87
    @31
    @11
    cc0
    cfz
    @27
    cS
    cN
    cmul
    oveq1
    oveq2d
    @87
    @37
    @22
    wceq
    @81
    @87
    @34
    @15
    @36
    @21
    vc
    @87
    @33
    @14
    @2
    @13
    @27
    cS
    crepr
    fveq2
    oveqd
    @87
    @36
    @21
    wceq
    @82
    @87
    @35
    @19
    @20
    cmul
    @87
    @29
    @1
    @18
    va
    @88
    prodeq1d
    oveq1d
    adantr
    sumeq12dv
    adantr
    sumeq12dv
    eqeq12d
    imbi12d
    wph
    @51
    @40
    wph
    cc0
    csn
    #
    @49
    vm
    csu
    #
    c1
    @50
    @42
    wph
    @90
    @2
    cc0
    @45
    co
    #
    @47
    cZ
    cc0
    cexp
    co
    #
    cmul
    co
    #
    vc
    csu
    #
    c0
    csn
    #
    @93
    vc
    csu
    #
    c1
    wph
    cc0
    cn0
    wcel
    @94
    cc
    wcel
    @90
    @94
    wceq
    0nn0
    wph
    @91
    @93
    vc
    wph
    @91
    @95
    cfn
    wph
    @91
    cc0
    cc0
    wceq
    #
    @95
    c0
    cif
    @95
    wph
    @2
    cN
    cc0
    @2
    cn
    wss
    wph
    cN
    fz1ssnn
    a1i
    wph
    0zd
    breprexp.n
    repr0
    @97
    @95
    c0
    cc0
    eqid
    iftruei
    syl6eq
    #
    c0
    snfi
    syl6eqel
    wph
    @93
    cc
    wcel
    @16
    @91
    wcel
    wph
    @93
    c1
    cc
    wph
    @93
    c1
    c1
    cmul
    co
    #
    c1
    wph
    @47
    c1
    @92
    c1
    cmul
    @47
    c1
    wceq
    wph
    @47
    c0
    @18
    va
    cprod
    c1
    @41
    c0
    @18
    va
    cc0
    fzo0
    #
    prodeq1i
    @18
    va
    prod0
    eqtri
    a1i
    wph
    cZ
    cc
    wcel
    #
    @92
    c1
    wceq
    breprexp.z
    cZ
    exp0
    syl
    #
    oveq12d
    #
    c1
    ax-1cn
    mulid1i
    syl6eq
    #
    ax-1cn
    syl6eqel
    adantr
    fsumcl
    @49
    @94
    vm
    cc0
    cn0
    @13
    cc0
    wceq
    #
    @46
    @91
    @48
    @93
    vc
    @13
    cc0
    @2
    @45
    oveq2
    @105
    @16
    @46
    wcel
    #
    wa
    #
    @20
    @92
    @47
    cmul
    @107
    @13
    cc0
    cZ
    cexp
    @105
    @106
    simpl
    oveq2d
    oveq2d
    sumeq12dv
    sumsn
    sylancr
    wph
    @91
    @95
    @93
    vc
    @98
    sumeq1d
    wph
    @96
    @41
    @4
    c0
    cfv
    #
    @5
    cfv
    #
    va
    cprod
    #
    @92
    cmul
    co
    #
    c1
    wph
    c0
    cvv
    wcel
    @111
    cc
    wcel
    @96
    @111
    wceq
    0ex
    wph
    @110
    @92
    wph
    @110
    c1
    cc
    @110
    c1
    wceq
    wph
    @110
    c0
    @109
    va
    cprod
    c1
    @41
    c0
    @109
    va
    @100
    prodeq1i
    @109
    va
    prod0
    eqtri
    a1i
    #
    ax-1cn
    syl6eqel
    wph
    @92
    c1
    cc
    @102
    ax-1cn
    syl6eqel
    mulcld
    @93
    @111
    vc
    c0
    cvv
    @16
    c0
    wceq
    #
    @47
    @110
    @92
    cmul
    @113
    @41
    @18
    @109
    va
    @113
    @18
    @109
    wceq
    va
    @41
    @113
    @17
    @108
    @5
    @4
    @16
    c0
    fveq1
    fveq2d
    ralrimivw
    prodeq2d
    oveq1d
    sumsn
    sylancr
    wph
    @111
    @99
    @93
    c1
    wph
    @110
    c1
    @92
    c1
    cmul
    @112
    @102
    oveq12d
    @103
    @104
    3eqtr2d
    eqtrd
    3eqtrd
    wph
    @44
    @89
    @49
    vm
    wph
    @44
    cc0
    cc0
    cfz
    co
    @89
    wph
    @43
    cc0
    cc0
    cfz
    wph
    cN
    wph
    cN
    breprexp.n
    nn0cnd
    mul02d
    oveq2d
    fz0sn
    syl6eq
    sumeq1d
    @42
    c1
    wceq
    wph
    @42
    c0
    @9
    va
    cprod
    c1
    @41
    c0
    @9
    va
    @100
    prodeq1i
    @9
    va
    prod0
    eqtri
    a1i
    3eqtr4rd
    a1d
    wph
    @52
    cn0
    wcel
    #
    wa
    #
    @65
    wa
    #
    @67
    @78
    @116
    @67
    wa
    #
    @115
    @53
    @54
    @2
    vj
    cv
    #
    vi
    cv
    #
    cL
    cfv
    #
    cfv
    #
    cZ
    @118
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    vi
    cprod
    #
    @57
    @2
    vn
    cv
    #
    @58
    co
    #
    @54
    @119
    vk
    cv
    #
    cfv
    #
    @120
    cfv
    #
    vi
    cprod
    #
    cZ
    @126
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    vn
    csu
    #
    wceq
    #
    wi
    #
    @67
    @78
    @115
    @65
    @67
    simpll
    @117
    @65
    @137
    @115
    @65
    @67
    simplr
    @64
    @136
    @53
    @64
    @55
    @57
    @127
    @60
    @132
    cmul
    co
    #
    vc
    csu
    #
    vn
    csu
    #
    wceq
    @136
    @63
    @140
    @55
    @57
    @62
    @139
    vm
    vn
    @13
    @126
    wceq
    #
    @59
    @127
    @61
    @138
    vc
    @13
    @126
    @2
    @58
    oveq2
    @141
    @61
    @138
    wceq
    @16
    @59
    wcel
    @141
    @20
    @132
    @60
    cmul
    @13
    @126
    cZ
    cexp
    oveq2
    oveq2d
    adantr
    sumeq12dv
    cbvsumv
    eqeq2i
    @55
    @125
    @140
    @135
    @55
    @54
    @2
    @3
    @120
    cfv
    #
    @7
    cmul
    co
    #
    vb
    csu
    #
    vi
    cprod
    @125
    @54
    @9
    @144
    va
    vi
    @4
    @119
    wceq
    #
    @2
    @8
    @143
    vb
    @145
    @3
    @2
    wcel
    #
    wa
    #
    @6
    @142
    @7
    cmul
    @147
    @3
    @5
    @120
    @147
    @4
    @119
    cL
    @145
    @146
    simpl
    fveq2d
    fveq1d
    oveq1d
    sumeq2dv
    cbvprodv
    @54
    @144
    @124
    vi
    @144
    @124
    wceq
    @119
    @54
    wcel
    #
    @2
    @143
    @123
    vb
    vj
    @3
    @118
    wceq
    @142
    @121
    @7
    @122
    cmul
    @3
    @118
    @120
    fveq2
    @3
    @118
    cZ
    cexp
    oveq2
    oveq12d
    cbvsumv
    a1i
    prodeq2i
    eqtri
    @57
    @139
    @134
    vn
    @139
    @134
    wceq
    @126
    @57
    wcel
    @139
    @127
    @54
    @119
    @16
    cfv
    #
    @120
    cfv
    #
    vi
    cprod
    #
    @132
    cmul
    co
    #
    vc
    csu
    @134
    @127
    @138
    @152
    vc
    @138
    @152
    wceq
    @16
    @127
    wcel
    @60
    @151
    @132
    cmul
    @54
    @18
    @150
    va
    vi
    @145
    @17
    @149
    @5
    @120
    @4
    @119
    cL
    fveq2
    @4
    @119
    @16
    fveq2
    fveq12d
    cbvprodv
    oveq1i
    a1i
    sumeq2i
    @127
    @152
    @133
    vc
    vk
    @16
    @128
    wceq
    #
    @151
    @131
    @132
    cmul
    @153
    @54
    @150
    @130
    vi
    @153
    @148
    wa
    #
    @149
    @129
    @120
    @154
    @119
    @16
    @128
    @153
    @148
    simpl
    fveq1d
    fveq2d
    prodeq2dv
    oveq1d
    cbvsumv
    eqtri
    a1i
    sumeq2i
    eqeq12i
    bitri
    imbi2i
    #
    sylib
    @116
    @67
    simpr
    @115
    @137
    wa
    #
    @67
    wa
    #
    cS
    @52
    vm
    cL
    cN
    cZ
    va
    vb
    vc
    wph
    cN
    cn0
    wcel
    @114
    @137
    @67
    breprexp.n
    ad3antrrr
    wph
    @0
    @114
    @137
    @67
    breprexp.s
    ad3antrrr
    #
    wph
    @101
    @114
    @137
    @67
    breprexp.z
    ad3antrrr
    wph
    @1
    cc
    cn
    cmap
    co
    cL
    wf
    @114
    @137
    @67
    breprexp.h
    ad3antrrr
    wph
    @114
    @137
    @67
    simpllr
    #
    @156
    @67
    simpr
    #
    @157
    @53
    @64
    @157
    @52
    @66
    cS
    @157
    cn0
    cr
    @52
    nn0ssre
    @159
    sseldi
    #
    @157
    @52
    c1
    @161
    @157
    1red
    readdcld
    #
    @157
    cn0
    cr
    cS
    nn0ssre
    @158
    sseldi
    @157
    @52
    @66
    @161
    @162
    @157
    @52
    @161
    ltp1d
    ltled
    @160
    letrd
    @157
    @137
    @65
    @115
    @137
    @67
    simplr
    @155
    sylibr
    mpd
    breprexplemc
    syl21anc
    ex
    nn0indd
    mpd
    mpdan
end
