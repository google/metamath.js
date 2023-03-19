include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cseq.mm"
include "ci.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "catan.mm"
include "cli.mm"
include "cn.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ax-icn.mm"
include "halfcl.mm"
include "mp1i.mm"
include "cvv.mm"
include "simpl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "negcld.mm"
include "absnegd.mm"
include "wceq.mm"
include "absmul.mm"
include "absi.mm"
include "oveq1i.mm"
include "cr.mm"
include "abscl.mm"
include "adantr.mm"
include "recnd.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "logtayl.mm"
include "syl2anc.mm"
include "ax-1cn.mm"
include "subneg.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "breqtrd.mm"
include "seqex.mm"
include "a1i.mm"
include "eqbrtrrd.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "eqeltrd.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "elfznn.mm"
include "eqtr4d.mm"
include "sersub.mm"
include "climsub.mm"
include "addcl.mm"
include "cdm.mm"
include "w3a.mm"
include "bndatandm.mm"
include "atandm2.mm"
include "sylib.mm"
include "simp3d.mm"
include "logcld.mm"
include "subcl.mm"
include "simp2d.mm"
include "neg2subd.mm"
include "subcld.mm"
include "negicn.mm"
include "2cnd.mm"
include "2ne0.mm"
include "div23d.mm"
include "oveq1d.mm"
include "mulassd.mm"
include "subdird.mm"
include "mulneg1.mm"
include "mulexpd.mm"
include "eqtr3d.mm"
include "divassd.mm"
include "divsubdird.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "isermulc2.mm"
include "atanval.mm"
include "syl.mm"
include "breqtrrd.mm"

theorem atantayl
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vm: setvar m
  assume atantayl.1: |- F = ( n e. NN |-> ( ( ( _i x. ( ( -u _i ^ n ) - ( _i ^ n ) ) ) / 2 ) x. ( ( A ^ n ) / n ) ) )

  disjoint A n
  disjoint k m
  disjoint k n
  disjoint A k
  disjoint m n
  disjoint A m
  disjoint F m
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> seq 1 ( + , F ) ~~> ( arctan ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    caddc
    cF
    c1
    cseq
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    cA
    cmul
    co
    #
    cmin
    co
    #
    clog
    cfv
    #
    c1
    @5
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cA
    catan
    cfv
    #
    cli
    @3
    @10
    @4
    vm
    vn
    cn
    @5
    cneg
    #
    vn
    cv
    #
    cexp
    co
    #
    @14
    cdiv
    co
    #
    @5
    @14
    cexp
    co
    #
    @14
    cdiv
    co
    #
    cmin
    co
    #
    cmpt
    #
    cF
    c1
    cn
    nnuz
    @3
    1zzd
    #
    ci
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @3
    ax-icn
    ci
    halfcl
    mp1i
    #
    @3
    caddc
    @20
    c1
    cseq
    #
    @9
    cneg
    #
    @7
    cneg
    #
    cmin
    co
    @10
    cli
    @3
    @26
    @27
    vk
    caddc
    vn
    cn
    @16
    cmpt
    #
    c1
    cseq
    #
    caddc
    vn
    cn
    @18
    cmpt
    #
    c1
    cseq
    #
    @25
    c1
    cvv
    cn
    nnuz
    @21
    @3
    @29
    c1
    @13
    cmin
    co
    #
    clog
    cfv
    #
    cneg
    #
    @26
    cli
    @3
    @13
    cc
    wcel
    #
    @13
    cabs
    cfv
    #
    c1
    clt
    wbr
    @29
    @34
    cli
    wbr
    @3
    @5
    @3
    @22
    @0
    @5
    cc
    wcel
    #
    ax-icn
    @0
    @2
    simpl
    #
    ci
    cA
    mulcl
    sylancr
    #
    negcld
    #
    @3
    @36
    @1
    c1
    clt
    @3
    @36
    @5
    cabs
    cfv
    #
    ci
    cabs
    cfv
    #
    @1
    cmul
    co
    #
    @1
    @3
    @5
    @39
    absnegd
    #
    @3
    @22
    @0
    @41
    @43
    wceq
    ax-icn
    @38
    ci
    cA
    absmul
    sylancr
    @3
    @43
    c1
    @1
    cmul
    co
    @1
    @42
    c1
    @1
    cmul
    absi
    oveq1i
    @3
    @1
    @3
    @1
    @0
    @1
    cr
    wcel
    @2
    cA
    abscl
    adantr
    recnd
    mulid2d
    syl5eq
    3eqtrd
    @0
    @2
    simpr
    eqbrtrd
    #
    @13
    vn
    logtayl
    syl2anc
    @3
    @33
    @9
    @3
    @32
    @8
    clog
    @3
    c1
    cc
    wcel
    #
    @37
    @32
    @8
    wceq
    ax-1cn
    @39
    c1
    @5
    subneg
    sylancr
    fveq2d
    negeqd
    breqtrd
    @25
    cvv
    wcel
    @3
    caddc
    @20
    c1
    seqex
    a1i
    @3
    @37
    @41
    c1
    clt
    wbr
    @31
    @27
    cli
    wbr
    @39
    @3
    @36
    @41
    c1
    clt
    @44
    @45
    eqbrtrrd
    @5
    vn
    logtayl
    syl2anc
    @3
    cn
    cc
    vk
    cv
    #
    @29
    @3
    vm
    @28
    c1
    cn
    nnuz
    @21
    @3
    vm
    cv
    #
    cn
    wcel
    #
    wa
    #
    @48
    @28
    cfv
    #
    @13
    @48
    cexp
    co
    #
    @48
    cdiv
    co
    #
    cc
    @49
    @51
    @53
    wceq
    @3
    vn
    @48
    @16
    @53
    cn
    @28
    @14
    @48
    wceq
    #
    @15
    @52
    @14
    @48
    cdiv
    @14
    @48
    @13
    cexp
    oveq2
    @54
    id
    #
    oveq12d
    #
    @28
    eqid
    @52
    @48
    cdiv
    ovex
    fvmpt
    adantl
    #
    @50
    @52
    @48
    @3
    @35
    @48
    cn0
    wcel
    #
    @52
    cc
    wcel
    @49
    @40
    @48
    nnnn0
    #
    @13
    @48
    expcl
    syl2an
    #
    @49
    @48
    cc
    wcel
    @3
    @48
    nncn
    adantl
    #
    @49
    @48
    cc0
    wne
    @3
    @48
    nnne0
    adantl
    #
    divcld
    #
    eqeltrd
    #
    serf
    ffvelrnda
    @3
    cn
    cc
    @47
    @31
    @3
    vm
    @30
    c1
    cn
    nnuz
    @21
    @50
    @48
    @30
    cfv
    #
    @5
    @48
    cexp
    co
    #
    @48
    cdiv
    co
    #
    cc
    @49
    @65
    @67
    wceq
    @3
    vn
    @48
    @18
    @67
    cn
    @30
    @54
    @17
    @66
    @14
    @48
    cdiv
    @14
    @48
    @5
    cexp
    oveq2
    @55
    oveq12d
    #
    @30
    eqid
    @66
    @48
    cdiv
    ovex
    fvmpt
    adantl
    #
    @50
    @66
    @48
    @3
    @37
    @58
    @66
    cc
    wcel
    @49
    @39
    @59
    @5
    @48
    expcl
    syl2an
    #
    @61
    @62
    divcld
    #
    eqeltrd
    #
    serf
    ffvelrnda
    @3
    @47
    cn
    wcel
    #
    wa
    #
    vm
    @28
    @30
    @20
    c1
    @47
    @74
    @47
    cn
    c1
    cuz
    cfv
    @3
    @73
    simpr
    nnuz
    syl6eleq
    @74
    @3
    @49
    @51
    cc
    wcel
    @48
    c1
    @47
    cfz
    co
    wcel
    #
    @3
    @73
    simpl
    #
    @48
    @47
    elfznn
    #
    @64
    syl2an
    @74
    @3
    @49
    @65
    cc
    wcel
    @75
    @76
    @77
    @72
    syl2an
    @74
    @3
    @49
    @48
    @20
    cfv
    #
    @51
    @65
    cmin
    co
    #
    wceq
    @75
    @76
    @77
    @50
    @78
    @53
    @67
    cmin
    co
    #
    @79
    @49
    @78
    @80
    wceq
    @3
    vn
    @48
    @19
    @80
    cn
    @20
    @54
    @16
    @53
    @18
    @67
    cmin
    @56
    @68
    oveq12d
    @20
    eqid
    @53
    @67
    cmin
    ovex
    fvmpt
    adantl
    #
    @50
    @51
    @53
    @65
    @67
    cmin
    @57
    @69
    oveq12d
    eqtr4d
    syl2an
    sersub
    climsub
    @3
    @9
    @7
    @3
    @8
    @3
    @46
    @37
    @8
    cc
    wcel
    ax-1cn
    @39
    c1
    @5
    addcl
    sylancr
    @3
    @0
    @6
    cc0
    wne
    #
    @8
    cc0
    wne
    #
    @3
    cA
    catan
    cdm
    wcel
    #
    @0
    @82
    @83
    w3a
    cA
    bndatandm
    #
    cA
    atandm2
    sylib
    #
    simp3d
    logcld
    @3
    @6
    @3
    @46
    @37
    @6
    cc
    wcel
    ax-1cn
    @39
    c1
    @5
    subcl
    sylancr
    @3
    @0
    @82
    @83
    @86
    simp2d
    logcld
    neg2subd
    breqtrd
    @50
    @78
    @80
    cc
    @81
    @50
    @53
    @67
    @63
    @71
    subcld
    eqeltrd
    @50
    ci
    ci
    cneg
    #
    @48
    cexp
    co
    #
    ci
    @48
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
    @48
    cexp
    co
    #
    @48
    cdiv
    co
    #
    cmul
    co
    #
    @4
    @80
    cmul
    co
    #
    @48
    cF
    cfv
    #
    @4
    @78
    cmul
    co
    @50
    @95
    @4
    @90
    cmul
    co
    #
    @94
    cmul
    co
    @4
    @90
    @94
    cmul
    co
    #
    cmul
    co
    @96
    @50
    @92
    @98
    @94
    cmul
    @50
    ci
    @90
    c2
    @22
    @50
    ax-icn
    a1i
    #
    @50
    @88
    @89
    @50
    @87
    cc
    wcel
    #
    @58
    @88
    cc
    wcel
    negicn
    @49
    @58
    @3
    @59
    adantl
    #
    @87
    @48
    expcl
    sylancr
    #
    @50
    @22
    @58
    @89
    cc
    wcel
    ax-icn
    @102
    ci
    @48
    expcl
    sylancr
    #
    subcld
    #
    @50
    2cnd
    c2
    cc0
    wne
    @50
    2ne0
    a1i
    div23d
    oveq1d
    @50
    @4
    @90
    @94
    @3
    @23
    @49
    @24
    adantr
    @105
    @50
    @93
    @48
    @3
    @0
    @58
    @93
    cc
    wcel
    @49
    @38
    @59
    cA
    @48
    expcl
    syl2an
    #
    @61
    @62
    divcld
    mulassd
    @50
    @99
    @80
    @4
    cmul
    @50
    @90
    @93
    cmul
    co
    #
    @48
    cdiv
    co
    @52
    @66
    cmin
    co
    #
    @48
    cdiv
    co
    @99
    @80
    @50
    @107
    @108
    @48
    cdiv
    @50
    @107
    @88
    @93
    cmul
    co
    #
    @89
    @93
    cmul
    co
    #
    cmin
    co
    @108
    @50
    @88
    @89
    @93
    @103
    @104
    @106
    subdird
    @50
    @52
    @109
    @66
    @110
    cmin
    @50
    @87
    cA
    cmul
    co
    #
    @48
    cexp
    co
    @52
    @109
    @50
    @111
    @13
    @48
    cexp
    @50
    @22
    @0
    @111
    @13
    wceq
    ax-icn
    @3
    @0
    @49
    @38
    adantr
    #
    ci
    cA
    mulneg1
    sylancr
    oveq1d
    @50
    @87
    cA
    @48
    @101
    @50
    negicn
    a1i
    @112
    @102
    mulexpd
    eqtr3d
    @50
    ci
    cA
    @48
    @100
    @112
    @102
    mulexpd
    oveq12d
    eqtr4d
    oveq1d
    @50
    @90
    @93
    @48
    @105
    @106
    @61
    @62
    divassd
    @50
    @52
    @66
    @48
    @60
    @70
    @61
    @62
    divsubdird
    3eqtr3d
    oveq2d
    3eqtrd
    @49
    @97
    @95
    wceq
    @3
    vn
    @48
    ci
    @87
    @14
    cexp
    co
    #
    ci
    @14
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
    @14
    cexp
    co
    #
    @14
    cdiv
    co
    #
    cmul
    co
    @95
    cn
    cF
    @54
    @117
    @92
    @119
    @94
    cmul
    @54
    @116
    @91
    c2
    cdiv
    @54
    @115
    @90
    ci
    cmul
    @54
    @113
    @88
    @114
    @89
    cmin
    @14
    @48
    @87
    cexp
    oveq2
    @14
    @48
    ci
    cexp
    oveq2
    oveq12d
    oveq2d
    oveq1d
    @54
    @118
    @93
    @14
    @48
    cdiv
    @14
    @48
    cA
    cexp
    oveq2
    @55
    oveq12d
    oveq12d
    atantayl.1
    @92
    @94
    cmul
    ovex
    fvmpt
    adantl
    @50
    @78
    @80
    @4
    cmul
    @81
    oveq2d
    3eqtr4d
    isermulc2
    @3
    @84
    @12
    @11
    wceq
    @85
    cA
    atanval
    syl
    breqtrrd
end
