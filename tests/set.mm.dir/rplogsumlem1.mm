include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "csu.mm"
include "csqrt.mm"
include "fzfid.mm"
include "wa.mm"
include "cuz.mm"
include "elfzuz.mm"
include "eluz2nn.mm"
include "syl.mm"
include "adantl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "uz2m1nn.mm"
include "nnmulcld.mm"
include "nndivred.mm"
include "fsumrecl.mm"
include "cr.mm"
include "crp.mm"
include "2re.mm"
include "rpsqrtcld.mm"
include "rerpdivcl.mm"
include "sylancr.mm"
include "resubcld.mm"
include "a1i.mm"
include "cle.mm"
include "wbr.mm"
include "rpred.mm"
include "nnred.mm"
include "peano2rem.mm"
include "remulcld.mm"
include "caddc.mm"
include "cc.mm"
include "wceq.mm"
include "nncnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "fveq2d.mm"
include "cc0.mm"
include "rpge0d.mm"
include "loglesqrt.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "readdcld.mm"
include "remulcl.mm"
include "lem1d.mm"
include "sqrtled.mm"
include "mpbid.mm"
include "subge0d.mm"
include "mpbird.mm"
include "leadd2dd.mm"
include "rpcnd.mm"
include "times2d.mm"
include "breqtrrd.mm"
include "lemul1ad.mm"
include "cexp.mm"
include "sqsqrtd.mm"
include "subcl.mm"
include "oveq12d.mm"
include "subsq.mm"
include "nncan.mm"
include "3eqtr3d.mm"
include "2cn.mm"
include "recnd.mm"
include "mulassd.mm"
include "3brtr3d.mm"
include "1red.mm"
include "lemul1d.mm"
include "mulid2d.mm"
include "mul32d.mm"
include "remsqsqrt.mm"
include "mul4d.mm"
include "eqtr3d.mm"
include "wne.mm"
include "rpcnne0d.mm"
include "divsubdiv.mm"
include "syl22anc.mm"
include "subdid.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "mulcld.mm"
include "rpmulcld.mm"
include "rerpdivcld.mm"
include "rpne0d.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "letrd.mm"
include "clt.mm"
include "wb.mm"
include "nngt0d.mm"
include "ledivmul.mm"
include "syl112anc.mm"
include "fsumle.mm"
include "oveq1.mm"
include "2m1e1.mm"
include "syl6eq.mm"
include "sqrt1.mm"
include "div1i.mm"
include "nnz.mm"
include "eluzp1p1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "telfsum.mm"
include "pncan.mm"
include "sumeq2dv.mm"
include "nncn.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "subge02.mm"
include "eqbrtrd.mm"

theorem rplogsumlem1
  let cA: class A
  let vn: setvar n
  let vk: setvar k
  let vp: setvar p

  disjoint A n
  disjoint k n
  disjoint k p
  disjoint A k
  disjoint n p
  disjoint A p
  assert |- ( A e. NN -> sum_ n e. ( 2 ... A ) ( ( log ` n ) / ( n x. ( n - 1 ) ) ) <_ 2 )

  proof
    cA
    cn
    wcel
    #
    c2
    cA
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
    @2
    c1
    cmin
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    vn
    csu
    @1
    c2
    @4
    csqrt
    cfv
    #
    cdiv
    co
    #
    c2
    @2
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    #
    vn
    csu
    #
    c2
    @0
    @1
    @6
    vn
    @0
    c2
    cA
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
    @5
    @15
    @2
    @15
    @2
    @14
    @2
    cn
    wcel
    #
    @0
    @14
    @2
    c2
    cuz
    cfv
    #
    wcel
    #
    @16
    @2
    c2
    cA
    elfzuz
    #
    @2
    eluz2nn
    syl
    adantl
    #
    nnrpd
    #
    relogcld
    #
    @15
    @2
    @4
    @20
    @15
    @18
    @4
    cn
    wcel
    @14
    @18
    @0
    @19
    adantl
    @2
    uz2m1nn
    syl
    #
    nnmulcld
    #
    nndivred
    #
    fsumrecl
    @0
    @1
    @11
    vn
    @13
    @15
    @8
    @10
    @15
    c2
    cr
    wcel
    #
    @7
    crp
    wcel
    @8
    cr
    wcel
    2re
    @15
    @4
    @15
    @4
    @23
    nnrpd
    #
    rpsqrtcld
    #
    c2
    @7
    rerpdivcl
    sylancr
    @15
    @26
    @9
    crp
    wcel
    @10
    cr
    wcel
    2re
    @15
    @2
    @21
    rpsqrtcld
    #
    c2
    @9
    rerpdivcl
    sylancr
    resubcld
    #
    fsumrecl
    @26
    @0
    2re
    a1i
    @0
    @1
    @6
    @11
    vn
    @13
    @25
    @30
    @15
    @6
    @11
    cle
    wbr
    #
    @3
    @5
    @11
    cmul
    co
    #
    cle
    wbr
    #
    @15
    @3
    @7
    @32
    @22
    @15
    @7
    @28
    rpred
    #
    @15
    @5
    @11
    @15
    @2
    @4
    @15
    @2
    @20
    nnred
    #
    @15
    @2
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @35
    @2
    peano2rem
    syl
    #
    remulcld
    #
    @30
    remulcld
    @15
    @4
    c1
    caddc
    co
    #
    clog
    cfv
    #
    @3
    @7
    cle
    @15
    @40
    @2
    clog
    @15
    @2
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @40
    @2
    wceq
    @15
    @2
    @20
    nncnd
    #
    ax-1cn
    @2
    c1
    npcan
    sylancl
    fveq2d
    @15
    @37
    cc0
    @4
    cle
    wbr
    #
    @41
    @7
    cle
    wbr
    @38
    @15
    @4
    @27
    rpge0d
    #
    @4
    loglesqrt
    syl2anc
    eqbrtrrd
    @15
    @7
    @9
    @7
    cmul
    co
    #
    c2
    @9
    @7
    cmin
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @32
    cle
    @15
    c1
    @7
    cmul
    co
    #
    @9
    @49
    cmul
    co
    #
    @7
    cmul
    co
    #
    @7
    @50
    cle
    @15
    c1
    @52
    cle
    wbr
    @51
    @53
    cle
    wbr
    @15
    @9
    @7
    caddc
    co
    #
    @48
    cmul
    co
    #
    @9
    c2
    cmul
    co
    #
    @48
    cmul
    co
    c1
    @52
    cle
    @15
    @54
    @56
    @48
    @15
    @9
    @7
    @15
    @9
    @29
    rpred
    #
    @34
    readdcld
    @15
    @9
    cr
    wcel
    @26
    @56
    cr
    wcel
    @57
    2re
    @9
    c2
    remulcl
    sylancl
    @15
    @9
    @7
    @57
    @34
    resubcld
    #
    @15
    cc0
    @48
    cle
    wbr
    @7
    @9
    cle
    wbr
    #
    @15
    @4
    @2
    cle
    wbr
    @59
    @15
    @2
    @35
    lem1d
    @15
    @4
    @2
    @38
    @46
    @35
    @15
    @2
    @21
    rpge0d
    #
    sqrtled
    mpbid
    #
    @15
    @9
    @7
    @57
    @34
    subge0d
    mpbird
    @15
    @54
    @9
    @9
    caddc
    co
    @56
    cle
    @15
    @7
    @9
    @9
    @34
    @57
    @57
    @61
    leadd2dd
    @15
    @9
    @15
    @9
    @29
    rpcnd
    #
    times2d
    breqtrrd
    lemul1ad
    @15
    @9
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    cmin
    co
    #
    @2
    @4
    cmin
    co
    #
    @55
    c1
    @15
    @63
    @2
    @64
    @4
    cmin
    @15
    @2
    @44
    sqsqrtd
    @15
    @4
    @15
    @42
    @43
    @4
    cc
    wcel
    @44
    ax-1cn
    @2
    c1
    subcl
    sylancl
    sqsqrtd
    oveq12d
    @15
    @9
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @65
    @55
    wceq
    @62
    @15
    @7
    @28
    rpcnd
    #
    @9
    @7
    subsq
    syl2anc
    @15
    @42
    @43
    @66
    c1
    wceq
    @44
    ax-1cn
    @2
    c1
    nncan
    sylancl
    3eqtr3d
    @15
    @9
    c2
    @48
    @62
    c2
    cc
    wcel
    #
    @15
    2cn
    a1i
    #
    @15
    @48
    @58
    recnd
    mulassd
    3brtr3d
    @15
    c1
    @52
    @7
    @15
    1red
    @15
    @9
    @49
    @57
    @15
    @26
    @48
    cr
    wcel
    @49
    cr
    wcel
    2re
    @58
    c2
    @48
    remulcl
    sylancr
    #
    remulcld
    @28
    lemul1d
    mpbid
    @15
    @7
    @69
    mulid2d
    @15
    @9
    @49
    @7
    @62
    @15
    @49
    @72
    recnd
    #
    @69
    mul32d
    3brtr3d
    @15
    @32
    @47
    @47
    cmul
    co
    #
    @49
    @47
    cdiv
    co
    #
    cmul
    co
    @47
    @47
    @75
    cmul
    co
    #
    cmul
    co
    @50
    @15
    @5
    @74
    @11
    @75
    cmul
    @15
    @9
    @9
    cmul
    co
    #
    @7
    @7
    cmul
    co
    #
    cmul
    co
    @5
    @74
    @15
    @77
    @2
    @78
    @4
    cmul
    @15
    @36
    cc0
    @2
    cle
    wbr
    @77
    @2
    wceq
    @35
    @60
    @2
    remsqsqrt
    syl2anc
    @15
    @37
    @45
    @78
    @4
    wceq
    @38
    @46
    @4
    remsqsqrt
    syl2anc
    oveq12d
    @15
    @9
    @9
    @7
    @7
    @62
    @62
    @69
    @69
    mul4d
    eqtr3d
    @15
    @11
    c2
    @9
    cmul
    co
    c2
    @7
    cmul
    co
    cmin
    co
    #
    @7
    @9
    cmul
    co
    #
    cdiv
    co
    #
    @75
    @15
    @70
    @70
    @68
    @7
    cc0
    wne
    wa
    @67
    @9
    cc0
    wne
    wa
    @11
    @81
    wceq
    @71
    @71
    @15
    @7
    @28
    rpcnne0d
    @15
    @9
    @29
    rpcnne0d
    c2
    c2
    @7
    @9
    divsubdiv
    syl22anc
    @15
    @49
    @79
    @47
    @80
    cdiv
    @15
    c2
    @9
    @7
    @71
    @62
    @69
    subdid
    @15
    @9
    @7
    @62
    @69
    mulcomd
    oveq12d
    eqtr4d
    oveq12d
    @15
    @47
    @47
    @75
    @15
    @9
    @7
    @62
    @69
    mulcld
    #
    @82
    @15
    @75
    @15
    @49
    @47
    @72
    @15
    @9
    @7
    @29
    @28
    rpmulcld
    #
    rerpdivcld
    recnd
    mulassd
    @15
    @76
    @49
    @47
    cmul
    @15
    @49
    @47
    @73
    @82
    @15
    @47
    @83
    rpne0d
    divcan2d
    oveq2d
    3eqtrd
    breqtrrd
    letrd
    @15
    @3
    cr
    wcel
    @11
    cr
    wcel
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    @31
    @33
    wb
    @22
    @30
    @39
    @15
    @5
    @24
    nngt0d
    @3
    @11
    @5
    ledivmul
    syl112anc
    mpbird
    fsumle
    @0
    @12
    c2
    c2
    cA
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    #
    c2
    cle
    @0
    @1
    @8
    c2
    @2
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    #
    vn
    csu
    c2
    c2
    cA
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    cmin
    co
    @12
    @86
    @0
    c2
    vk
    cv
    #
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cdiv
    co
    #
    @8
    @90
    c2
    vn
    vk
    @95
    c2
    cA
    @96
    @2
    wceq
    #
    @98
    @7
    c2
    cdiv
    @100
    @97
    @4
    csqrt
    @96
    @2
    c1
    cmin
    oveq1
    fveq2d
    oveq2d
    @96
    @87
    wceq
    #
    @98
    @89
    c2
    cdiv
    @101
    @97
    @88
    csqrt
    @96
    @87
    c1
    cmin
    oveq1
    fveq2d
    oveq2d
    @96
    c2
    wceq
    #
    @99
    c2
    c1
    cdiv
    co
    c2
    @102
    @98
    c1
    c2
    cdiv
    @102
    @98
    c1
    csqrt
    cfv
    c1
    @102
    @97
    c1
    csqrt
    @102
    @97
    c2
    c1
    cmin
    co
    c1
    @96
    c2
    c1
    cmin
    oveq1
    2m1e1
    syl6eq
    fveq2d
    sqrt1
    syl6eq
    oveq2d
    c2
    2cn
    div1i
    syl6eq
    @96
    @92
    wceq
    #
    @98
    @94
    c2
    cdiv
    @103
    @97
    @93
    csqrt
    @96
    @92
    c1
    cmin
    oveq1
    fveq2d
    oveq2d
    cA
    nnz
    @0
    @92
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @17
    @92
    @105
    wcel
    cA
    c1
    cuz
    cfv
    cn
    c1
    cA
    eluzp1p1
    nnuz
    eleq2s
    c2
    @104
    cuz
    df-2
    fveq2i
    syl6eleqr
    @0
    @96
    c2
    @92
    cfz
    co
    wcel
    #
    wa
    #
    @99
    @107
    @26
    @98
    crp
    wcel
    @99
    cr
    wcel
    2re
    @107
    @97
    @107
    @97
    @106
    @97
    cn
    wcel
    #
    @0
    @106
    @96
    @17
    wcel
    @108
    @96
    c2
    @92
    elfzuz
    @96
    uz2m1nn
    syl
    adantl
    nnrpd
    rpsqrtcld
    c2
    @98
    rerpdivcl
    sylancr
    recnd
    telfsum
    @0
    @1
    @91
    @11
    vn
    @15
    @90
    @10
    @8
    cmin
    @15
    @89
    @9
    c2
    cdiv
    @15
    @88
    @2
    csqrt
    @15
    @42
    @43
    @88
    @2
    wceq
    @44
    ax-1cn
    @2
    c1
    pncan
    sylancl
    fveq2d
    oveq2d
    oveq2d
    sumeq2dv
    @0
    @95
    @85
    c2
    cmin
    @0
    @94
    @84
    c2
    cdiv
    @0
    @93
    cA
    csqrt
    @0
    cA
    cc
    wcel
    @43
    @93
    cA
    wceq
    cA
    nncn
    ax-1cn
    cA
    c1
    pncan
    sylancl
    fveq2d
    oveq2d
    oveq2d
    3eqtr3d
    @0
    cc0
    @85
    cle
    wbr
    #
    @86
    c2
    cle
    wbr
    #
    @0
    @85
    @0
    c2
    crp
    wcel
    @84
    crp
    wcel
    @85
    crp
    wcel
    2rp
    @0
    cA
    cA
    nnrp
    rpsqrtcld
    c2
    @84
    rpdivcl
    sylancr
    #
    rpge0d
    @0
    @26
    @85
    cr
    wcel
    @109
    @110
    wb
    2re
    @0
    @85
    @111
    rpred
    c2
    @85
    subge02
    sylancr
    mpbid
    eqbrtrd
    letrd
end
