include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "csu.mm"
include "cmul.mm"
include "caddc.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "2re.mm"
include "fzfid.mm"
include "wa.mm"
include "cuz.mm"
include "elfzuz.mm"
include "adantl.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "elfznn.mm"
include "nnrecred.mm"
include "resqcld.mm"
include "nnrp.mm"
include "peano2re.mm"
include "syl.mm"
include "recnd.mm"
include "2timesd.mm"
include "cmin.mm"
include "cc0.mm"
include "cem.mm"
include "cicc.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "harmonicbnd3.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "0re.mm"
include "emre.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "subge0d.mm"
include "mpbid.mm"
include "lediv1dd.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "wss.mm"
include "cz.mm"
include "elfzelz.mm"
include "peano2zm.mm"
include "nnred.mm"
include "lem1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "fsumless.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "letrd.mm"
include "fsumle.mm"
include "le2addd.mm"
include "cfzo.mm"
include "oveq1.mm"
include "sumeq1d.mm"
include "jca.mm"
include "c0.mm"
include "1m1e0.mm"
include "syl6eq.mm"
include "fz10.mm"
include "sum0.mm"
include "peano2nn.mm"
include "syl6eleq.mm"
include "fsumparts.mm"
include "nnz.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "pncan.mm"
include "oveq2.mm"
include "fsumm1.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "nnne0d.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "sumeq12rdv.mm"
include "nncn.mm"
include "oveq12d.mm"
include "sqvald.mm"
include "0cn.mm"
include "mul01i.mm"
include "a1i.mm"
include "sqcld.mm"
include "subid1d.mm"
include "divrec2d.mm"
include "3eqtr3rd.mm"
include "subaddd.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"
include "cfl.mm"
include "flid.mm"
include "nnre.mm"
include "nnge1.mm"
include "harmonicubnd.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "fsumge0.mm"
include "log1.mm"
include "crp.mm"
include "1rp.mm"
include "logleb.mm"
include "syl5eqbrr.mm"
include "lep1d.mm"
include "le2sqd.mm"
include "2pos.mm"
include "lemuldiv2.mm"

theorem logdivbnd
  let vn: setvar n
  let cN: class N
  let vi: setvar i
  let vm: setvar m

  disjoint N n
  disjoint i m
  disjoint i n
  disjoint N i
  disjoint m n
  disjoint N m
  assert |- ( N e. NN -> sum_ n e. ( 1 ... N ) ( ( log ` n ) / n ) <_ ( ( ( ( log ` N ) + 1 ) ^ 2 ) / 2 ) )

  proof
    cN
    cn
    wcel
    #
    c2
    c1
    cN
    cfz
    co
    #
    vn
    cv
    #
    clog
    cfv
    #
    @2
    cdiv
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cN
    clog
    cfv
    #
    c1
    caddc
    co
    #
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @5
    @9
    c2
    cdiv
    co
    cle
    wbr
    #
    @0
    @6
    @1
    c1
    vi
    cv
    #
    cdiv
    co
    #
    vi
    csu
    #
    c2
    cexp
    co
    #
    @9
    @0
    c2
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    2re
    @0
    @1
    @4
    vn
    @0
    c1
    cN
    fzfid
    #
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @2
    @20
    @2
    @20
    @2
    @20
    @2
    c1
    cuz
    cfv
    #
    cn
    @19
    @2
    @21
    wcel
    @0
    @2
    c1
    cN
    elfzuz
    adantl
    #
    nnuz
    syl6eleqr
    #
    nnrpd
    #
    relogcld
    #
    @23
    nndivred
    #
    fsumrecl
    #
    c2
    @5
    remulcl
    sylancr
    @0
    @14
    @0
    @1
    @13
    vi
    @18
    @0
    @12
    @1
    wcel
    #
    wa
    #
    @12
    @28
    @12
    cn
    wcel
    #
    @0
    @12
    cN
    elfznn
    adantl
    #
    nnrecred
    #
    fsumrecl
    #
    resqcld
    @0
    @8
    @0
    @7
    cr
    wcel
    @8
    cr
    wcel
    @0
    cN
    cN
    nnrp
    #
    relogcld
    #
    @7
    peano2re
    syl
    #
    resqcld
    #
    @0
    @6
    @5
    @5
    caddc
    co
    #
    @15
    cle
    @0
    @5
    @0
    @5
    @27
    recnd
    2timesd
    @0
    @38
    @1
    c1
    @2
    cfz
    co
    #
    @13
    vi
    csu
    #
    @2
    cdiv
    co
    #
    vn
    csu
    #
    @1
    c1
    @2
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    vi
    csu
    #
    @2
    cdiv
    co
    #
    vn
    csu
    #
    caddc
    co
    #
    @15
    cle
    @0
    @5
    @5
    @42
    @47
    @27
    @27
    @0
    @1
    @41
    vn
    @18
    @20
    @40
    @2
    @20
    @39
    @13
    vi
    @20
    c1
    @2
    fzfid
    #
    @20
    @12
    @39
    wcel
    #
    wa
    #
    @12
    @50
    @30
    @20
    @12
    @2
    elfznn
    adantl
    #
    nnrecred
    #
    fsumrecl
    #
    @23
    nndivred
    #
    fsumrecl
    #
    @0
    @1
    @46
    vn
    @18
    @20
    @45
    @2
    @20
    @44
    @13
    vi
    @20
    c1
    @43
    fzfid
    @20
    @12
    @44
    wcel
    #
    wa
    @12
    @57
    @30
    @20
    @12
    @43
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    @23
    nndivred
    #
    fsumrecl
    #
    @0
    @1
    @4
    @41
    vn
    @18
    @26
    @55
    @20
    @4
    @46
    @41
    @26
    @59
    @55
    @20
    @3
    @45
    @2
    @25
    @58
    @24
    @20
    cc0
    @45
    @3
    cmin
    co
    #
    cle
    wbr
    #
    @3
    @45
    cle
    wbr
    @20
    @61
    cc0
    cem
    cicc
    co
    #
    wcel
    #
    @62
    @20
    @45
    @43
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    @61
    @63
    @20
    @66
    @3
    @45
    cmin
    @20
    @65
    @2
    clog
    @20
    @2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @65
    @2
    wceq
    @20
    @2
    @23
    nncnd
    #
    ax-1cn
    @2
    c1
    npcan
    sylancl
    fveq2d
    oveq2d
    @20
    @2
    cn
    wcel
    @43
    cn0
    wcel
    @67
    @63
    wcel
    @23
    @2
    nnm1nn0
    vi
    @43
    harmonicbnd3
    3syl
    eqeltrrd
    @64
    @61
    cr
    wcel
    @62
    @61
    cem
    cle
    wbr
    cc0
    cem
    @61
    0re
    emre
    elicc2i
    simp2bi
    syl
    @20
    @45
    @3
    @58
    @25
    subge0d
    mpbid
    lediv1dd
    #
    @20
    @45
    @40
    cle
    wbr
    #
    @46
    @41
    cle
    wbr
    #
    @20
    @39
    @13
    @44
    vi
    @49
    @53
    @51
    @13
    @51
    @12
    @51
    @12
    @52
    nnrpd
    rpreccld
    rpge0d
    @20
    @2
    @43
    cuz
    cfv
    wcel
    #
    @44
    @39
    wss
    @20
    @43
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @43
    @2
    cle
    wbr
    @74
    @20
    @76
    @75
    @19
    @76
    @0
    @2
    c1
    cN
    elfzelz
    adantl
    #
    @2
    peano2zm
    syl
    @77
    @20
    @2
    @20
    @2
    @23
    nnred
    #
    lem1d
    @43
    @2
    eluz2
    syl3anbrc
    @43
    c1
    @2
    fzss2
    syl
    fsumless
    @20
    @45
    cr
    wcel
    @40
    cr
    wcel
    @2
    cr
    wcel
    cc0
    @2
    clt
    wbr
    @72
    @73
    wb
    @58
    @54
    @78
    @20
    @2
    @23
    nngt0d
    @45
    @40
    @2
    lediv1
    syl112anc
    mpbid
    letrd
    fsumle
    @0
    @1
    @4
    @46
    vn
    @18
    @26
    @59
    @71
    fsumle
    le2addd
    @0
    @15
    @42
    cmin
    co
    #
    @47
    wceq
    @48
    @15
    wceq
    @0
    c1
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @45
    c1
    @2
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    vi
    csu
    #
    @45
    cmin
    co
    #
    cmul
    co
    #
    vn
    csu
    c1
    @80
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    vi
    csu
    #
    @90
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
    @81
    @86
    @85
    cmul
    co
    #
    vn
    csu
    #
    cmin
    co
    @47
    @79
    @0
    c1
    vm
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    vi
    csu
    #
    @45
    @85
    cc0
    vn
    vm
    @90
    c1
    @80
    @99
    @45
    @85
    cc0
    @90
    @96
    @2
    wceq
    #
    @99
    @45
    wceq
    #
    @101
    @100
    @98
    @44
    @13
    vi
    @100
    @97
    @43
    c1
    cfz
    @96
    @2
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    #
    @102
    jca
    @96
    @82
    wceq
    #
    @99
    @85
    wceq
    #
    @104
    @103
    @98
    @84
    @13
    vi
    @103
    @97
    @83
    c1
    cfz
    @96
    @82
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    #
    @105
    jca
    @96
    c1
    wceq
    #
    @99
    cc0
    wceq
    #
    @107
    @106
    @99
    c0
    @13
    vi
    csu
    cc0
    @106
    @98
    c0
    @13
    vi
    @106
    @98
    c1
    cc0
    cfz
    co
    c0
    @106
    @97
    cc0
    c1
    cfz
    @106
    @97
    c1
    c1
    cmin
    co
    cc0
    @96
    c1
    c1
    cmin
    oveq1
    1m1e0
    syl6eq
    oveq2d
    fz10
    syl6eq
    sumeq1d
    @13
    vi
    sum0
    syl6eq
    #
    @108
    jca
    @96
    @80
    wceq
    #
    @99
    @90
    wceq
    #
    @110
    @109
    @98
    @89
    @13
    vi
    @109
    @97
    @88
    c1
    cfz
    @96
    @80
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    #
    @111
    jca
    @0
    @80
    cn
    @21
    cN
    peano2nn
    nnuz
    syl6eleq
    @0
    @96
    c1
    @80
    cfz
    co
    wcel
    wa
    #
    @99
    @112
    @98
    @13
    vi
    @112
    c1
    @97
    fzfid
    @112
    @12
    @98
    wcel
    #
    wa
    @12
    @113
    @30
    @112
    @12
    @97
    elfznn
    adantl
    nnrecred
    fsumrecl
    recnd
    #
    @114
    fsumparts
    @0
    @81
    @1
    @87
    @46
    vn
    @0
    @1
    @81
    @0
    cN
    cz
    wcel
    #
    @1
    @81
    wceq
    cN
    nnz
    #
    c1
    cN
    fzval3
    syl
    eqcomd
    #
    @20
    @87
    @45
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    @46
    @20
    @86
    @118
    @45
    cmul
    @20
    @86
    @45
    @118
    caddc
    co
    #
    @45
    cmin
    co
    @118
    @20
    @85
    @119
    @45
    cmin
    @20
    @85
    @40
    @119
    @20
    @84
    @39
    @13
    vi
    @20
    @83
    @2
    c1
    cfz
    @20
    @68
    @69
    @83
    @2
    wceq
    @70
    ax-1cn
    @2
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    #
    @20
    @13
    @118
    vi
    c1
    @2
    @22
    @51
    @13
    @53
    recnd
    @12
    @2
    c1
    cdiv
    oveq2
    fsumm1
    eqtrd
    oveq1d
    @20
    @45
    @118
    @20
    @45
    @58
    recnd
    #
    @20
    @118
    @20
    @2
    @23
    nnrecred
    recnd
    pncan2d
    eqtrd
    #
    oveq2d
    @20
    @45
    @2
    @121
    @70
    @20
    @2
    @23
    nnne0d
    #
    divrecd
    eqtr4d
    sumeq12rdv
    @0
    @93
    @15
    @95
    @42
    cmin
    @0
    @93
    @15
    cc0
    cmin
    co
    @15
    @0
    @91
    @15
    @92
    cc0
    cmin
    @0
    @91
    @14
    @14
    cmul
    co
    @15
    @0
    @90
    @14
    @90
    @14
    cmul
    @0
    @89
    @1
    @13
    vi
    @0
    @88
    cN
    c1
    cfz
    @0
    cN
    cc
    wcel
    @69
    @88
    cN
    wceq
    cN
    nncn
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    #
    @124
    oveq12d
    @0
    @14
    @0
    @14
    @33
    recnd
    #
    sqvald
    eqtr4d
    @92
    cc0
    wceq
    @0
    cc0
    0cn
    mul01i
    a1i
    oveq12d
    @0
    @15
    @0
    @14
    @125
    sqcld
    #
    subid1d
    eqtrd
    @0
    @81
    @1
    @94
    @41
    vn
    @117
    @20
    @94
    @118
    @40
    cmul
    co
    @41
    @20
    @86
    @118
    @85
    @40
    cmul
    @122
    @120
    oveq12d
    @20
    @40
    @2
    @20
    @40
    @54
    recnd
    @70
    @123
    divrec2d
    eqtr4d
    sumeq12rdv
    oveq12d
    3eqtr3rd
    @0
    @15
    @42
    @47
    @126
    @0
    @42
    @56
    recnd
    @0
    @47
    @60
    recnd
    subaddd
    mpbid
    breqtrd
    eqbrtrd
    @0
    @14
    @8
    cle
    wbr
    @15
    @9
    cle
    wbr
    @0
    c1
    cN
    cfl
    cfv
    #
    cfz
    co
    #
    @13
    vi
    csu
    #
    @14
    @8
    cle
    @0
    @128
    @1
    @13
    vi
    @0
    @127
    cN
    c1
    cfz
    @0
    @115
    @127
    cN
    wceq
    @116
    cN
    flid
    syl
    oveq2d
    sumeq1d
    @0
    cN
    cr
    wcel
    c1
    cN
    cle
    wbr
    #
    @129
    @8
    cle
    wbr
    cN
    nnre
    cN
    nnge1
    #
    cN
    vi
    harmonicubnd
    syl2anc
    eqbrtrrd
    @0
    @14
    @8
    @33
    @36
    @0
    @1
    @13
    vi
    @18
    @32
    @29
    @13
    @29
    @12
    @29
    @12
    @31
    nnrpd
    rpreccld
    rpge0d
    fsumge0
    @0
    cc0
    @7
    @8
    cc0
    cr
    wcel
    @0
    0re
    a1i
    @35
    @36
    @0
    cc0
    c1
    clog
    cfv
    #
    @7
    cle
    log1
    @0
    @130
    @132
    @7
    cle
    wbr
    #
    @131
    @0
    c1
    crp
    wcel
    cN
    crp
    wcel
    @130
    @133
    wb
    1rp
    @34
    c1
    cN
    logleb
    sylancr
    mpbid
    syl5eqbrr
    @0
    @7
    @35
    lep1d
    letrd
    le2sqd
    mpbid
    letrd
    @0
    @17
    @9
    cr
    wcel
    @16
    cc0
    c2
    clt
    wbr
    #
    @10
    @11
    wb
    @27
    @37
    @16
    @0
    2re
    a1i
    @134
    @0
    2pos
    a1i
    @5
    @9
    c2
    lemuldiv2
    syl112anc
    mpbid
end
