include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cprime.mm"
include "cdif.mm"
include "cv.mm"
include "cvma.mm"
include "cfv.mm"
include "csu.mm"
include "c2.mm"
include "clog.mm"
include "caddc.mm"
include "c4.mm"
include "c6.mm"
include "cdp2.mm"
include "cdp.mm"
include "csqrt.mm"
include "cmul.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "c3.mm"
include "clt.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfid.mm"
include "diffi.mm"
include "syl.mm"
include "wa.mm"
include "cn.mm"
include "cr.mm"
include "wf.mm"
include "vmaf.mm"
include "a1i.mm"
include "wss.mm"
include "fz1ssnn.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "fsumrecl.mm"
include "crp.mm"
include "2rp.mm"
include "relogcld.mm"
include "cn0.mm"
include "1nn0.mm"
include "4re.mm"
include "2re.mm"
include "6re.mm"
include "pm3.2i.mm"
include "dp2cl.mm"
include "ax-mp.mm"
include "dpcl.mm"
include "mp2an.mm"
include "nnred.mm"
include "nnrpd.mm"
include "rpge0d.mm"
include "resqrtcld.mm"
include "remulcld.mm"
include "0nn0.mm"
include "0re.mm"
include "1re.mm"
include "cchp.mm"
include "ccht.mm"
include "cmin.mm"
include "cin.mm"
include "cz.mm"
include "wceq.mm"
include "nnzd.mm"
include "chpvalz.mm"
include "chtvalz.mm"
include "inss2.mm"
include "vmaprm.mm"
include "sumeq2dv.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "recnd.mm"
include "fsumcl.mm"
include "infi.mm"
include "inss1.mm"
include "sstri.mm"
include "c0.mm"
include "inindif.mm"
include "inundif.mm"
include "eqcomi.mm"
include "fsumsplit.mm"
include "comraddd.mm"
include "mvrraddd.mm"
include "eqtr2d.mm"
include "wbr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wral.mm"
include "ax-ros336.mm"
include "rspcdva.mm"
include "eqbrtrd.mm"
include "log2le1.mm"
include "cdc.mm"
include "c7.mm"
include "cexp.mm"
include "10nn0.mm"
include "7nn0.mm"
include "nn0expcli.mm"
include "nn0rei.mm"
include "cdiv.mm"
include "w3a.mm"
include "0z.mm"
include "3z.mm"
include "3pm3.2i.mm"
include "1lt10.mm"
include "3pos.mm"
include "ltexp2a.mm"
include "numexp0.mm"
include "cc.mm"
include "wne.mm"
include "recni.mm"
include "10pos.mm"
include "gtneii.mm"
include "4z.mm"
include "expm1.mm"
include "mp3an.mm"
include "4m1e3.mm"
include "oveq2i.mm"
include "4nn0.mm"
include "nn0cni.mm"
include "divrec2.mm"
include "3eqtr3ri.mm"
include "3brtr4i.mm"
include "1rp.mm"
include "dp0h.mm"
include "oveq1i.mm"
include "breqtrri.mm"
include "c5.mm"
include "4p1e5.mm"
include "5nn0.mm"
include "nn0zi.mm"
include "dpexpp1.mm"
include "rpdp2cl.mm"
include "5p1e6.mm"
include "6nn0.mm"
include "6p1e7.mm"
include "3eqtrri.mm"
include "syl6breqr.mm"
include "rpdpcl.mm"
include "2nn0.mm"
include "deccl.mm"
include "cle.mm"
include "nn0ge0i.mm"
include "expmul.mm"
include "7t2e14.mm"
include "eqtr3i.mm"
include "fveq2i.mm"
include "expgt0.mm"
include "ltleii.mm"
include "sqrtsq.mm"
include "4lt10.mm"
include "1lt2.mm"
include "decltc.mm"
include "wb.mm"
include "sqrtlt.mm"
include "mpbi.mm"
include "eqbrtrri.mm"
include "sqrtled.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "ltmul2dd.mm"
include "lttrd.mm"
include "lt2addd.mm"
include "nfv.mm"
include "nfcv.mm"
include "2prm.mm"
include "wn.mm"
include "elndif.mm"
include "syl6eq.mm"
include "2cnd.mm"
include "2ne0.mm"
include "logcld.mm"
include "fsumsplitsn.mm"
include "3rp.mm"
include "1p0e1.mm"
include "4cn.mm"
include "addid1i.mm"
include "2cn.mm"
include "3nn0.mm"
include "eqid.mm"
include "6cn.mm"
include "2p1e3.mm"
include "decadd.mm"
include "dpadd.mm"
include "dpadd2.mm"
include "adddird.mm"
include "syl5eqr.mm"
include "3brtr4d.mm"

theorem hgt750lemd
  let wph: wff ph
  let vi: setvar i
  let cN: class N
  let vj: setvar j
  let vx: setvar x
  assume hgt750lemc.n: |- ( ph -> N e. NN )
  assume hgt750lemd.0: |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N )

  disjoint N i
  disjoint i ph
  disjoint N j
  disjoint i j
  disjoint N x
  disjoint ph x
  disjoint i x
  assert |- ( ph -> sum_ i e. ( ( ( 1 ... N ) \ Prime ) u. { 2 } ) ( Lam ` i ) < ( ( 1 . _ 4 _ 2 _ 6 3 ) x. ( sqrt ` N ) ) )

  proof
    wph
    c1
    cN
    cfz
    co
    #
    cprime
    cdif
    #
    vi
    cv
    #
    cvma
    cfv
    #
    vi
    csu
    #
    c2
    clog
    cfv
    #
    caddc
    co
    c1
    c4
    c2
    c6
    c2
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp
    co
    #
    cN
    csqrt
    cfv
    #
    cmul
    co
    #
    cc0
    cc0
    cc0
    cc0
    c1
    cdp2
    #
    cdp2
    #
    cdp2
    #
    cdp
    co
    #
    @10
    cmul
    co
    #
    caddc
    co
    #
    @1
    c2
    csn
    cun
    @3
    vi
    csu
    c1
    c4
    c2
    c6
    c3
    cdp2
    #
    cdp2
    #
    cdp2
    cdp
    co
    #
    @10
    cmul
    co
    #
    clt
    wph
    @4
    @5
    @11
    @16
    wph
    @1
    @3
    vi
    wph
    @0
    cfn
    wcel
    #
    @1
    cfn
    wcel
    wph
    c1
    cN
    fzfid
    #
    @0
    cprime
    diffi
    syl
    #
    wph
    @2
    @1
    wcel
    wa
    #
    cn
    cr
    @2
    cvma
    cn
    cr
    cvma
    wf
    #
    @25
    vmaf
    a1i
    wph
    @1
    cn
    @2
    wph
    @0
    cn
    cprime
    @0
    cn
    wss
    wph
    cN
    fz1ssnn
    #
    a1i
    #
    ssdifssd
    sselda
    ffvelrnd
    #
    fsumrecl
    wph
    c2
    c2
    crp
    wcel
    wph
    2rp
    a1i
    relogcld
    #
    wph
    @9
    @10
    @9
    cr
    wcel
    #
    wph
    c1
    cn0
    wcel
    @8
    cr
    wcel
    #
    @31
    1nn0
    c4
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    wa
    @32
    @33
    @34
    4re
    c2
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    @34
    @35
    @36
    2re
    c6
    cr
    wcel
    #
    @35
    wa
    @36
    @37
    @35
    6re
    2re
    pm3.2i
    c6
    c2
    dp2cl
    ax-mp
    pm3.2i
    c2
    @6
    dp2cl
    ax-mp
    pm3.2i
    c4
    @7
    dp2cl
    ax-mp
    c1
    @8
    dpcl
    mp2an
    a1i
    #
    wph
    cN
    wph
    cN
    hgt750lemc.n
    nnred
    #
    wph
    cN
    wph
    cN
    hgt750lemc.n
    nnrpd
    #
    rpge0d
    #
    resqrtcld
    #
    remulcld
    wph
    @15
    @10
    @15
    cr
    wcel
    #
    wph
    cc0
    cn0
    wcel
    @14
    cr
    wcel
    #
    @43
    0nn0
    cc0
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    wa
    @44
    @45
    @46
    0re
    @45
    @12
    cr
    wcel
    #
    wa
    @46
    @45
    @47
    0re
    @45
    c1
    cr
    wcel
    #
    wa
    @47
    @45
    @48
    0re
    1re
    pm3.2i
    cc0
    c1
    dp2cl
    ax-mp
    pm3.2i
    cc0
    @12
    dp2cl
    ax-mp
    pm3.2i
    cc0
    @13
    dp2cl
    ax-mp
    cc0
    @14
    dpcl
    mp2an
    a1i
    #
    @42
    remulcld
    #
    wph
    @4
    cN
    cchp
    cfv
    #
    cN
    ccht
    cfv
    #
    cmin
    co
    #
    @11
    clt
    wph
    @53
    @0
    @3
    vi
    csu
    #
    @0
    cprime
    cin
    #
    @3
    vi
    csu
    #
    cmin
    co
    @4
    wph
    @51
    @54
    @52
    @56
    cmin
    wph
    cN
    cz
    wcel
    #
    @51
    @54
    wceq
    wph
    cN
    hgt750lemc.n
    nnzd
    #
    vi
    cN
    chpvalz
    syl
    wph
    @52
    @55
    @2
    clog
    cfv
    #
    vi
    csu
    #
    @56
    wph
    @57
    @52
    @60
    wceq
    @58
    vi
    cN
    chtvalz
    syl
    wph
    @55
    @3
    @59
    vi
    wph
    @2
    @55
    wcel
    wa
    #
    @2
    cprime
    wcel
    @3
    @59
    wceq
    wph
    @55
    cprime
    @2
    @55
    cprime
    wss
    wph
    @0
    cprime
    inss2
    a1i
    sselda
    @2
    vmaprm
    syl
    sumeq2dv
    eqtr4d
    oveq12d
    wph
    @54
    @4
    @56
    wph
    @1
    @3
    vi
    @24
    @25
    @3
    @29
    recnd
    #
    fsumcl
    #
    wph
    @55
    @3
    vi
    wph
    @22
    @55
    cfn
    wcel
    @23
    @0
    cprime
    infi
    syl
    @61
    @3
    @61
    cn
    cr
    @2
    cvma
    @26
    @61
    vmaf
    a1i
    wph
    @55
    cn
    @2
    @55
    cn
    wss
    wph
    @55
    @0
    cn
    @0
    cprime
    inss1
    @27
    sstri
    a1i
    sselda
    ffvelrnd
    recnd
    fsumcl
    #
    wph
    @54
    @56
    @4
    @64
    @63
    wph
    @55
    @1
    @3
    @0
    vi
    @55
    @1
    cin
    c0
    wceq
    wph
    @0
    cprime
    inindif
    a1i
    @0
    @55
    @1
    cun
    #
    wceq
    wph
    @65
    @0
    @0
    cprime
    inundif
    eqcomi
    a1i
    @23
    wph
    @2
    @0
    wcel
    wa
    #
    @3
    @66
    cn
    cr
    @2
    cvma
    @26
    @66
    vmaf
    a1i
    wph
    @0
    cn
    @2
    @28
    sselda
    ffvelrnd
    recnd
    fsumsplit
    comraddd
    mvrraddd
    eqtr2d
    wph
    vx
    cv
    #
    cchp
    cfv
    #
    @67
    ccht
    cfv
    #
    cmin
    co
    #
    @9
    @67
    csqrt
    cfv
    #
    cmul
    co
    #
    clt
    wbr
    #
    @53
    @11
    clt
    wbr
    vx
    crp
    cN
    @67
    cN
    wceq
    #
    @70
    @53
    @72
    @11
    clt
    @74
    @68
    @51
    @69
    @52
    cmin
    @67
    cN
    cchp
    fveq2
    @67
    cN
    ccht
    fveq2
    oveq12d
    @74
    @71
    @10
    @9
    cmul
    @67
    cN
    csqrt
    fveq2
    oveq2d
    breq12d
    @73
    vx
    crp
    wral
    wph
    vx
    ax-ros336
    a1i
    @40
    rspcdva
    eqbrtrd
    wph
    @5
    c1
    @16
    @30
    @48
    wph
    1re
    a1i
    #
    @50
    @5
    c1
    clt
    wbr
    wph
    log2le1
    a1i
    wph
    c1
    @15
    c1
    cc0
    cdc
    #
    c7
    cexp
    co
    #
    cmul
    co
    #
    @16
    @75
    wph
    @15
    @77
    @49
    @77
    cr
    wcel
    #
    wph
    @77
    @76
    c7
    10nn0
    7nn0
    nn0expcli
    nn0rei
    #
    a1i
    #
    remulcld
    @50
    wph
    c1
    cc0
    c1
    cdp
    co
    #
    @76
    c4
    cexp
    co
    #
    cmul
    co
    #
    @78
    clt
    c1
    @84
    clt
    wbr
    wph
    c1
    c1
    @76
    cdiv
    co
    #
    @83
    cmul
    co
    #
    @84
    clt
    @76
    cc0
    cexp
    co
    #
    @76
    c3
    cexp
    co
    #
    c1
    @86
    clt
    @76
    cr
    wcel
    #
    cc0
    cz
    wcel
    #
    c3
    cz
    wcel
    #
    w3a
    c1
    @76
    clt
    wbr
    #
    cc0
    c3
    clt
    wbr
    #
    wa
    @87
    @88
    clt
    wbr
    @89
    @90
    @91
    @76
    10nn0
    nn0rei
    #
    0z
    3z
    3pm3.2i
    @92
    @93
    1lt10
    3pos
    pm3.2i
    @76
    cc0
    c3
    ltexp2a
    mp2an
    @87
    c1
    @76
    10nn0
    numexp0
    eqcomi
    @76
    c4
    c1
    cmin
    co
    #
    cexp
    co
    #
    @83
    @76
    cdiv
    co
    #
    @88
    @86
    @76
    cc
    wcel
    #
    @76
    cc0
    wne
    #
    c4
    cz
    wcel
    @96
    @97
    wceq
    @76
    @94
    recni
    #
    cc0
    @76
    0re
    10pos
    gtneii
    #
    4z
    @76
    c4
    expm1
    mp3an
    @95
    c3
    @76
    cexp
    4m1e3
    oveq2i
    @83
    cc
    wcel
    @98
    @99
    @97
    @86
    wceq
    @83
    @76
    c4
    10nn0
    4nn0
    nn0expcli
    nn0cni
    @100
    @101
    @83
    @76
    divrec2
    mp3an
    3eqtr3ri
    3brtr4i
    @82
    @85
    @83
    cmul
    c1
    1rp
    dp0h
    oveq1i
    breqtrri
    a1i
    @84
    cc0
    @12
    cdp
    co
    @76
    c5
    cexp
    co
    cmul
    co
    cc0
    @13
    cdp
    co
    @76
    c6
    cexp
    co
    cmul
    co
    @78
    cc0
    c1
    c4
    c5
    0nn0
    1rp
    4p1e5
    4z
    c5
    5nn0
    nn0zi
    #
    dpexpp1
    cc0
    @12
    c5
    c6
    0nn0
    cc0
    c1
    0nn0
    1rp
    rpdp2cl
    #
    5p1e6
    @102
    c6
    6nn0
    nn0zi
    #
    dpexpp1
    cc0
    @13
    c6
    c7
    0nn0
    cc0
    @12
    0nn0
    @103
    rpdp2cl
    #
    6p1e7
    @104
    c7
    7nn0
    nn0zi
    #
    dpexpp1
    3eqtrri
    syl6breqr
    wph
    @77
    @10
    @15
    @81
    @42
    @15
    crp
    wcel
    wph
    cc0
    @14
    0nn0
    cc0
    @13
    0nn0
    @105
    rpdp2cl
    rpdpcl
    a1i
    wph
    @77
    @76
    c2
    c7
    cdc
    #
    cexp
    co
    #
    csqrt
    cfv
    #
    @10
    @81
    wph
    @108
    @108
    cr
    wcel
    #
    wph
    @108
    @76
    @107
    10nn0
    c2
    c7
    2nn0
    7nn0
    deccl
    #
    nn0expcli
    #
    nn0rei
    #
    a1i
    #
    cc0
    @108
    cle
    wbr
    #
    wph
    @108
    @112
    nn0ge0i
    #
    a1i
    #
    resqrtcld
    @42
    @77
    @109
    clt
    wbr
    wph
    @76
    c1
    c4
    cdc
    #
    cexp
    co
    #
    csqrt
    cfv
    #
    @77
    @109
    clt
    @77
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @120
    @77
    @121
    @119
    csqrt
    @76
    c7
    c2
    cmul
    co
    #
    cexp
    co
    #
    @121
    @119
    @98
    c7
    cn0
    wcel
    c2
    cn0
    wcel
    @124
    @121
    wceq
    @100
    7nn0
    2nn0
    @76
    c7
    c2
    expmul
    mp3an
    @123
    @118
    @76
    cexp
    7t2e14
    oveq2i
    eqtr3i
    fveq2i
    @79
    cc0
    @77
    cle
    wbr
    @122
    @77
    wceq
    @80
    cc0
    @77
    0re
    @80
    @89
    c7
    cz
    wcel
    cc0
    @76
    clt
    wbr
    #
    cc0
    @77
    clt
    wbr
    @94
    @106
    10pos
    @76
    c7
    expgt0
    mp3an
    ltleii
    @77
    sqrtsq
    mp2an
    eqtr3i
    @119
    @108
    clt
    wbr
    #
    @120
    @109
    clt
    wbr
    #
    @89
    @118
    cz
    wcel
    #
    @107
    cz
    wcel
    #
    w3a
    @92
    @118
    @107
    clt
    wbr
    #
    wa
    @126
    @89
    @128
    @129
    @94
    @118
    c1
    c4
    1nn0
    4nn0
    deccl
    #
    nn0zi
    #
    @107
    @111
    nn0zi
    3pm3.2i
    @92
    @130
    1lt10
    c1
    c2
    c4
    c7
    1nn0
    2nn0
    4nn0
    7nn0
    4lt10
    1lt2
    decltc
    pm3.2i
    @76
    @118
    @107
    ltexp2a
    mp2an
    @119
    cr
    wcel
    #
    cc0
    @119
    cle
    wbr
    #
    wa
    @110
    @115
    wa
    @126
    @127
    wb
    @133
    @134
    @119
    @76
    @118
    10nn0
    @131
    nn0expcli
    nn0rei
    #
    cc0
    @119
    0re
    @135
    @89
    @128
    @125
    cc0
    @119
    clt
    wbr
    @94
    @132
    10pos
    @76
    @118
    expgt0
    mp3an
    ltleii
    pm3.2i
    @110
    @115
    @113
    @116
    pm3.2i
    @119
    @108
    sqrtlt
    mp2an
    mpbi
    eqbrtrri
    a1i
    wph
    @108
    cN
    cle
    wbr
    @109
    @10
    cle
    wbr
    hgt750lemd.0
    wph
    @108
    cN
    @114
    @117
    @39
    @41
    sqrtled
    mpbid
    ltletrd
    ltmul2dd
    lttrd
    lttrd
    lt2addd
    wph
    @1
    c2
    @3
    @5
    vi
    cprime
    wph
    vi
    nfv
    vi
    @5
    nfcv
    @24
    c2
    cprime
    wcel
    #
    wph
    2prm
    a1i
    #
    wph
    @136
    c2
    @1
    wcel
    wn
    @137
    c2
    cprime
    @0
    elndif
    syl
    @62
    @2
    c2
    wceq
    @3
    c2
    cvma
    cfv
    #
    @5
    @2
    c2
    cvma
    fveq2
    @136
    @138
    @5
    wceq
    2prm
    c2
    vmaprm
    ax-mp
    syl6eq
    wph
    c2
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    logcld
    fsumsplitsn
    wph
    @21
    @9
    @15
    caddc
    co
    #
    @10
    cmul
    co
    @17
    @139
    @20
    @10
    cmul
    c4
    @7
    cc0
    @13
    c4
    @19
    c1
    cc0
    c1
    4nn0
    c2
    @6
    2nn0
    c6
    c2
    6nn0
    2rp
    rpdp2cl
    #
    rpdp2cl
    0nn0
    @105
    4nn0
    c2
    @18
    2nn0
    c6
    c3
    6nn0
    3rp
    rpdp2cl
    #
    rpdp2cl
    1nn0
    0nn0
    1p0e1
    c2
    @6
    cc0
    @12
    c2
    @18
    c4
    cc0
    c4
    2nn0
    @140
    0nn0
    @103
    2nn0
    @141
    4nn0
    0nn0
    c4
    4cn
    addid1i
    c6
    c2
    cc0
    c1
    c6
    c3
    c2
    cc0
    c2
    6nn0
    2rp
    0nn0
    1rp
    6nn0
    3rp
    2nn0
    0nn0
    c2
    2cn
    addid1i
    c6
    c2
    cc0
    c1
    c6
    c3
    6nn0
    2nn0
    0nn0
    1nn0
    6nn0
    3nn0
    c6
    c2
    cc0
    c1
    c6
    c3
    c6
    c2
    cdc
    #
    cc0
    c1
    cdc
    #
    6nn0
    2nn0
    0nn0
    1nn0
    @142
    eqid
    @143
    eqid
    c6
    6cn
    addid1i
    2p1e3
    decadd
    dpadd
    dpadd2
    dpadd2
    dpadd2
    oveq1i
    wph
    @9
    @15
    @10
    wph
    @9
    @38
    recnd
    wph
    @15
    @49
    recnd
    wph
    @10
    @42
    recnd
    adddird
    syl5eqr
    3brtr4d
end
