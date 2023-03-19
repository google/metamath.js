include "crp.mm"
include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "clog.mm"
include "cmul.mm"
include "csu.mm"
include "cchp.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "wtru.mm"
include "caddc.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "cr.mm"
include "rpre.mm"
include "chpcl.mm"
include "syl.mm"
include "recnd.mm"
include "cn0.mm"
include "cn.mm"
include "cle.mm"
include "wbr.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "relogcl.mm"
include "subcld.mm"
include "mulcld.mm"
include "fzfid.mm"
include "elfznn.mm"
include "adantl.mm"
include "1rp.mm"
include "rpaddcl.mm"
include "mpan2.mm"
include "resubcld.mm"
include "remulcld.mm"
include "fsumcl.mm"
include "rpcnne0.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "sub32d.mm"
include "subdid.mm"
include "oveq1d.mm"
include "cfzo.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "jca.mm"
include "log1.mm"
include "syl6eq.mm"
include "1m1e0.mm"
include "c2.mm"
include "clt.mm"
include "2pos.mm"
include "wb.mm"
include "0re.mm"
include "chpeq0.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "cuz.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "nnred.mm"
include "peano2rem.mm"
include "fsumparts.mm"
include "cz.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "npcan.mm"
include "eqtr4d.mm"
include "nnm1nn0.mm"
include "chpp1.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "nn0red.mm"
include "vmacl.mm"
include "pncan2d.mm"
include "eqtrd.mm"
include "mulcomd.mm"
include "sumeq12rdv.mm"
include "nn0cnd.mm"
include "chpfl.mm"
include "0cn.mm"
include "mul01i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "subid1d.mm"
include "3eqtr3d.mm"
include "3eqtr4d.mm"
include "div23.mm"
include "3eqtr3rd.mm"
include "mpteq2ia.mm"
include "cvv.mm"
include "ovexd.mm"
include "cof.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "eqidd.mm"
include "offval2.mm"
include "chpo1ub.mm"
include "crli.mm"
include "0red.mm"
include "1red.mm"
include "divrcnv.mm"
include "mp1i.mm"
include "rpreccl.mm"
include "rpred.mm"
include "flle.mm"
include "leadd1dd.mm"
include "logled.mm"
include "mpbid.mm"
include "lesub1dd.mm"
include "logdifbnd.mm"
include "letrd.mm"
include "ad2antrl.mm"
include "fllep1.mm"
include "logleb.mm"
include "mpdan.mm"
include "subge0d.mm"
include "mpbird.mm"
include "rlimsqz2.mm"
include "rlimo1.mm"
include "o1mul.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "wss.mm"
include "nnrp.mm"
include "ssriv.mm"
include "sselda.mm"
include "rerpdivcl.mm"
include "mpancom.mm"
include "cabs.mm"
include "chpge0.mm"
include "lemul1ad.mm"
include "lep1d.mm"
include "mulge0d.mm"
include "absidd.mm"
include "rpregt0.mm"
include "divge0.mm"
include "syl21anc.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divrec2d.mm"
include "3brtr4d.mm"
include "o1le.mm"
include "o1res2.mm"
include "o1fsum.mm"
include "o1sub2.mm"
include "syl5eqelr.mm"
include "trud.mm"

theorem selberg2lem
  let vx: setvar x
  let vn: setvar n
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vy: setvar y

  disjoint n x
  disjoint c d
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( x e. RR+ |-> ( ( sum_ n e. ( 1 ... ( |_ ` x ) ) ( ( Lam ` n ) x. ( log ` n ) ) - ( ( psi ` x ) x. ( log ` x ) ) ) / x ) ) e. O(1)

  proof
    vx
    crp
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    #
    cvma
    cfv
    #
    @3
    clog
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @0
    cchp
    cfv
    #
    @0
    clog
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @0
    cdiv
    co
    #
    cmpt
    #
    co1
    wcel
    wtru
    @13
    vx
    crp
    @8
    @0
    cdiv
    co
    #
    @1
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @9
    cmin
    co
    #
    cmul
    co
    #
    @2
    @3
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @5
    cmin
    co
    #
    @3
    cchp
    cfv
    #
    cmul
    co
    #
    vn
    csu
    #
    @0
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    co1
    vx
    crp
    @26
    @12
    @0
    crp
    wcel
    #
    @8
    @17
    cmul
    co
    #
    @24
    cmin
    co
    #
    @0
    cdiv
    co
    #
    @28
    @0
    cdiv
    co
    #
    @25
    cmin
    co
    #
    @12
    @26
    @27
    @28
    cc
    wcel
    @24
    cc
    wcel
    @0
    cc
    wcel
    @0
    cc0
    wne
    wa
    #
    @30
    @32
    wceq
    @27
    @8
    @17
    @27
    @8
    @27
    @0
    cr
    wcel
    #
    @8
    cr
    wcel
    @0
    rpre
    #
    @0
    chpcl
    syl
    recnd
    #
    @27
    @16
    @9
    @27
    @16
    @27
    @15
    @27
    @15
    @27
    @1
    cn0
    wcel
    #
    @15
    cn
    wcel
    @27
    @34
    cc0
    @0
    cle
    wbr
    wa
    @37
    @0
    rprege0
    @0
    flge0nn0
    syl
    #
    @1
    nn0p1nn
    syl
    #
    nnrpd
    #
    relogcld
    #
    recnd
    #
    @27
    @9
    @0
    relogcl
    #
    recnd
    #
    subcld
    #
    mulcld
    @27
    @2
    @23
    vn
    @27
    c1
    @1
    fzfid
    @27
    @3
    @2
    wcel
    #
    wa
    #
    @3
    crp
    wcel
    #
    @23
    cc
    wcel
    #
    @47
    @3
    @46
    @3
    cn
    wcel
    #
    @27
    @3
    @1
    elfznn
    adantl
    #
    nnrpd
    #
    @48
    @23
    @48
    @21
    @22
    @48
    @20
    @5
    @48
    @19
    @48
    c1
    crp
    wcel
    #
    @19
    crp
    wcel
    #
    1rp
    @3
    c1
    rpaddcl
    mpan2
    #
    relogcld
    #
    @3
    relogcl
    #
    resubcld
    #
    @48
    @3
    cr
    wcel
    #
    @22
    cr
    wcel
    #
    @3
    rpre
    #
    @3
    chpcl
    syl
    #
    remulcld
    #
    recnd
    #
    syl
    fsumcl
    #
    @0
    rpcnne0
    #
    @28
    @24
    @0
    divsubdir
    syl3anc
    @27
    @29
    @11
    @0
    cdiv
    @27
    @8
    @16
    cmul
    co
    #
    @10
    cmin
    co
    #
    @24
    cmin
    co
    @67
    @24
    cmin
    co
    #
    @10
    cmin
    co
    @29
    @11
    @27
    @67
    @10
    @24
    @27
    @8
    @16
    @36
    @42
    mulcld
    #
    @27
    @8
    @9
    @36
    @44
    mulcld
    @65
    sub32d
    @27
    @28
    @68
    @24
    cmin
    @27
    @8
    @16
    @9
    @36
    @42
    @44
    subdid
    oveq1d
    @27
    @7
    @69
    @10
    cmin
    @27
    c1
    @15
    cfzo
    co
    #
    @5
    @19
    c1
    cmin
    co
    #
    cchp
    cfv
    #
    @3
    c1
    cmin
    co
    #
    cchp
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    @16
    @15
    c1
    cmin
    co
    #
    cchp
    cfv
    #
    cmul
    co
    #
    cc0
    cc0
    cmul
    co
    #
    cmin
    co
    #
    @71
    @21
    @73
    cmul
    co
    #
    vn
    csu
    #
    cmin
    co
    @7
    @69
    @27
    vm
    cv
    #
    clog
    cfv
    #
    @5
    @20
    cc0
    vn
    vm
    @16
    c1
    @15
    @85
    c1
    cmin
    co
    #
    cchp
    cfv
    #
    @75
    @73
    cc0
    @79
    @85
    @3
    wceq
    #
    @86
    @5
    wceq
    @88
    @75
    wceq
    @85
    @3
    clog
    fveq2
    @89
    @87
    @74
    cchp
    @85
    @3
    c1
    cmin
    oveq1
    fveq2d
    jca
    @85
    @19
    wceq
    #
    @86
    @20
    wceq
    @88
    @73
    wceq
    @85
    @19
    clog
    fveq2
    @90
    @87
    @72
    cchp
    @85
    @19
    c1
    cmin
    oveq1
    fveq2d
    jca
    @85
    c1
    wceq
    #
    @86
    cc0
    wceq
    @88
    cc0
    wceq
    @91
    @86
    c1
    clog
    cfv
    cc0
    @85
    c1
    clog
    fveq2
    log1
    syl6eq
    @91
    @88
    cc0
    cchp
    cfv
    #
    cc0
    @91
    @87
    cc0
    cchp
    @91
    @87
    c1
    c1
    cmin
    co
    cc0
    @85
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    fveq2d
    @92
    cc0
    wceq
    #
    cc0
    c2
    clt
    wbr
    #
    2pos
    cc0
    cr
    wcel
    @93
    @94
    wb
    0re
    cc0
    chpeq0
    ax-mp
    mpbir
    syl6eq
    jca
    @85
    @15
    wceq
    #
    @86
    @16
    wceq
    @88
    @79
    wceq
    @85
    @15
    clog
    fveq2
    @95
    @87
    @78
    cchp
    @85
    @15
    c1
    cmin
    oveq1
    fveq2d
    jca
    @27
    @15
    cn
    c1
    cuz
    cfv
    @39
    nnuz
    syl6eleq
    @27
    @85
    c1
    @15
    cfz
    co
    wcel
    #
    wa
    #
    @86
    @97
    @85
    @97
    @85
    @96
    @85
    cn
    wcel
    @27
    @85
    @15
    elfznn
    adantl
    #
    nnrpd
    relogcld
    recnd
    @97
    @88
    @97
    @87
    cr
    wcel
    #
    @88
    cr
    wcel
    @97
    @85
    cr
    wcel
    @99
    @97
    @85
    @98
    nnred
    @85
    peano2rem
    syl
    @87
    chpcl
    syl
    recnd
    fsumparts
    @27
    @71
    @2
    @77
    @6
    vn
    @27
    @2
    @71
    @27
    @1
    cz
    wcel
    @2
    @71
    wceq
    @27
    @1
    @38
    nn0zd
    c1
    @1
    fzval3
    syl
    eqcomd
    #
    @47
    @77
    @5
    @4
    cmul
    co
    @6
    @47
    @76
    @4
    @5
    cmul
    @47
    @76
    @75
    @4
    caddc
    co
    #
    @75
    cmin
    co
    @4
    @47
    @73
    @101
    @75
    cmin
    @47
    @73
    @74
    c1
    caddc
    co
    #
    cchp
    cfv
    #
    @75
    @102
    cvma
    cfv
    #
    caddc
    co
    #
    @101
    @47
    @72
    @102
    cchp
    @47
    @72
    @3
    @102
    @47
    @3
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @72
    @3
    wceq
    @47
    @3
    @51
    nncnd
    #
    ax-1cn
    @3
    c1
    pncan
    sylancl
    #
    @47
    @106
    @107
    @102
    @3
    wceq
    @108
    ax-1cn
    @3
    c1
    npcan
    sylancl
    #
    eqtr4d
    fveq2d
    @47
    @74
    cn0
    wcel
    #
    @103
    @105
    wceq
    @47
    @50
    @111
    @51
    @3
    nnm1nn0
    syl
    #
    @74
    chpp1
    syl
    @47
    @104
    @4
    @75
    caddc
    @47
    @102
    @3
    cvma
    @110
    fveq2d
    oveq2d
    3eqtrd
    oveq1d
    @47
    @75
    @4
    @47
    @75
    @47
    @74
    cr
    wcel
    @75
    cr
    wcel
    @47
    @74
    @112
    nn0red
    @74
    chpcl
    syl
    recnd
    @47
    @4
    @47
    @50
    @4
    cr
    wcel
    @51
    @3
    vmacl
    syl
    recnd
    #
    pncan2d
    eqtrd
    oveq2d
    @47
    @4
    @5
    @113
    @47
    @5
    @47
    @3
    @52
    relogcld
    recnd
    mulcomd
    eqtr4d
    sumeq12rdv
    @27
    @82
    @67
    @84
    @24
    cmin
    @27
    @82
    @67
    cc0
    cmin
    co
    @67
    @27
    @80
    @67
    @81
    cc0
    cmin
    @27
    @80
    @16
    @8
    cmul
    co
    @67
    @27
    @79
    @8
    @16
    cmul
    @27
    @79
    @1
    cchp
    cfv
    #
    @8
    @27
    @78
    @1
    cchp
    @27
    @1
    cc
    wcel
    @107
    @78
    @1
    wceq
    @27
    @1
    @38
    nn0cnd
    ax-1cn
    @1
    c1
    pncan
    sylancl
    fveq2d
    @27
    @34
    @114
    @8
    wceq
    @35
    @0
    chpfl
    syl
    eqtrd
    oveq2d
    @27
    @16
    @8
    @42
    @36
    mulcomd
    eqtrd
    @81
    cc0
    wceq
    @27
    cc0
    0cn
    mul01i
    a1i
    oveq12d
    @27
    @67
    @70
    subid1d
    eqtrd
    @27
    @71
    @2
    @83
    @23
    vn
    @100
    @47
    @73
    @22
    @21
    cmul
    @47
    @72
    @3
    cchp
    @109
    fveq2d
    oveq2d
    sumeq12rdv
    oveq12d
    3eqtr3d
    oveq1d
    3eqtr4d
    oveq1d
    @27
    @31
    @18
    @25
    cmin
    @27
    @8
    cc
    wcel
    @17
    cc
    wcel
    #
    @33
    @31
    @18
    wceq
    @36
    @45
    @66
    @8
    @17
    @0
    div23
    syl3anc
    oveq1d
    3eqtr3rd
    mpteq2ia
    wtru
    vx
    crp
    @18
    @25
    cvv
    wtru
    @27
    wa
    #
    @14
    @17
    cmul
    ovexd
    @116
    @24
    @0
    cdiv
    ovexd
    wtru
    vx
    crp
    @14
    cmpt
    #
    vx
    crp
    @17
    cmpt
    #
    cmul
    cof
    co
    #
    vx
    crp
    @18
    cmpt
    co1
    wtru
    vx
    crp
    @14
    @17
    cmul
    @117
    @118
    cvv
    cvv
    cc
    crp
    cvv
    wcel
    wtru
    crp
    cr
    reex
    rpssre
    ssexi
    a1i
    @116
    @8
    @0
    cdiv
    ovexd
    @27
    @115
    wtru
    @45
    adantl
    wtru
    @117
    eqidd
    wtru
    @118
    eqidd
    offval2
    wtru
    @117
    co1
    wcel
    @118
    co1
    wcel
    #
    @119
    co1
    wcel
    vx
    chpo1ub
    wtru
    @118
    cc0
    crli
    wbr
    @120
    wtru
    vx
    crp
    c1
    @0
    cdiv
    co
    #
    @17
    cc0
    c1
    wtru
    0red
    wtru
    1red
    #
    @107
    vx
    crp
    @121
    cmpt
    cc0
    crli
    wbr
    wtru
    ax-1cn
    c1
    vx
    divrcnv
    mp1i
    @27
    @121
    cr
    wcel
    wtru
    @27
    @121
    @0
    rpreccl
    rpred
    #
    adantl
    @27
    @17
    cr
    wcel
    wtru
    @27
    @16
    @9
    @41
    @43
    resubcld
    #
    adantl
    @27
    @17
    @121
    cle
    wbr
    wtru
    c1
    @0
    cle
    wbr
    #
    @27
    @17
    @0
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @9
    cmin
    co
    @121
    @124
    @27
    @127
    @9
    @27
    @126
    @27
    @53
    @126
    crp
    wcel
    1rp
    @0
    c1
    rpaddcl
    mpan2
    #
    relogcld
    #
    @43
    resubcld
    @123
    @27
    @16
    @127
    @9
    @41
    @129
    @43
    @27
    @15
    @126
    cle
    wbr
    @16
    @127
    cle
    wbr
    @27
    @1
    @0
    c1
    @27
    @1
    @38
    nn0red
    @35
    @27
    1red
    @27
    @34
    @1
    @0
    cle
    wbr
    @35
    @0
    flle
    syl
    leadd1dd
    @27
    @15
    @126
    @40
    @128
    logled
    mpbid
    lesub1dd
    @0
    logdifbnd
    letrd
    ad2antrl
    @27
    cc0
    @17
    cle
    wbr
    #
    wtru
    @125
    @27
    @130
    @9
    @16
    cle
    wbr
    #
    @27
    @0
    @15
    cle
    wbr
    #
    @131
    @27
    @34
    @132
    @35
    @0
    fllep1
    syl
    @27
    @15
    crp
    wcel
    @132
    @131
    wb
    @40
    @0
    @15
    logleb
    mpdan
    mpbid
    @27
    @16
    @9
    @41
    @43
    subge0d
    mpbird
    ad2antrl
    rlimsqz2
    cc0
    @118
    rlimo1
    syl
    @117
    @118
    o1mul
    sylancr
    eqeltrrd
    wtru
    vx
    @23
    vn
    cc
    wtru
    @50
    wa
    @48
    @49
    wtru
    cn
    crp
    @3
    cn
    crp
    wss
    wtru
    vm
    cn
    crp
    @85
    nnrp
    ssriv
    a1i
    #
    sselda
    @64
    syl
    wtru
    vn
    cn
    crp
    @23
    @133
    wtru
    vn
    crp
    @22
    @3
    cdiv
    co
    #
    @23
    c1
    cr
    @122
    vn
    crp
    @134
    cmpt
    co1
    wcel
    wtru
    vn
    chpo1ub
    a1i
    @48
    @134
    cr
    wcel
    #
    wtru
    @60
    @48
    @135
    @62
    @22
    @3
    rerpdivcl
    mpancom
    #
    adantl
    @48
    @49
    wtru
    @64
    adantl
    @48
    @23
    cabs
    cfv
    #
    @134
    cabs
    cfv
    #
    cle
    wbr
    wtru
    c1
    @3
    cle
    wbr
    @48
    @23
    c1
    @3
    cdiv
    co
    #
    @22
    cmul
    co
    #
    @137
    @138
    cle
    @48
    @21
    @139
    @22
    @58
    @48
    @139
    @3
    rpreccl
    rpred
    @62
    @48
    @59
    cc0
    @22
    cle
    wbr
    #
    @61
    @3
    chpge0
    syl
    #
    @3
    logdifbnd
    lemul1ad
    @48
    @23
    @63
    @48
    @21
    @22
    @58
    @62
    @48
    cc0
    @21
    cle
    wbr
    @5
    @20
    cle
    wbr
    #
    @48
    @3
    @19
    cle
    wbr
    #
    @143
    @48
    @3
    @61
    lep1d
    @48
    @54
    @144
    @143
    wb
    @55
    @3
    @19
    logleb
    mpdan
    mpbid
    @48
    @20
    @5
    @56
    @57
    subge0d
    mpbird
    @142
    mulge0d
    absidd
    @48
    @138
    @134
    @140
    @48
    @134
    @136
    @48
    @60
    @141
    @59
    cc0
    @3
    clt
    wbr
    wa
    cc0
    @134
    cle
    wbr
    @62
    @142
    @3
    rpregt0
    @22
    @3
    divge0
    syl21anc
    absidd
    @48
    @22
    @3
    @48
    @22
    @62
    recnd
    @3
    rpcn
    @3
    rpne0
    divrec2d
    eqtrd
    3brtr4d
    ad2antrl
    o1le
    o1res2
    o1fsum
    o1sub2
    syl5eqelr
    trud
end
