include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "cdig.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "cmin.mm"
include "nnnn0.mm"
include "blennn0em1.mm"
include "sylan2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "adantr.mm"
include "sumeq2dv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "simpr.mm"
include "cc.mm"
include "nncn.mm"
include "pncan1.mm"
include "syl.mm"
include "sylan9eq.mm"
include "eqeq2d.mm"
include "cfz.mm"
include "cz.mm"
include "nnz.mm"
include "adantl.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "sumeq1d.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "a1i.mm"
include "elfzelz.mm"
include "nn0rp0.mm"
include "ad4antlr.mm"
include "digvalnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "2nn0.mm"
include "elfznn0.mm"
include "nn0expcld.mm"
include "mulcld.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "2cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "fsum1p.mm"
include "0dig2nn0e.mm"
include "syl2anr.mm"
include "cr.mm"
include "1re.mm"
include "mul02lem2.mm"
include "1z.mm"
include "0p1e1.mm"
include "eqeltri.mm"
include "2cnd.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "oveq1i.mm"
include "eleq2s.mm"
include "expcld.mm"
include "fsumshftm.mm"
include "ad4antr.mm"
include "elfzonn0.mm"
include "dignn0ehalf.mm"
include "expp1d.mm"
include "elfzoelz.mm"
include "2re.mm"
include "reexpcld.mm"
include "recnd.mm"
include "w3a.mm"
include "mulass.mm"
include "eqtrd.mm"
include "0cn.mm"
include "fzoval.mm"
include "oveq2d.mm"
include "cfn.mm"
include "fzofi.mm"
include "peano2zd.mm"
include "peano2nn0.mm"
include "fsumcl.mm"
include "addid2d.mm"
include "fsummulc1.mm"
include "3eqtr4d.mm"
include "3eqtrd.mm"
include "weq.mm"
include "cbvsumv.mm"
include "biimpac.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan1d.mm"
include "ad3antlr.mm"
include "3eqtrrd.mm"
include "ex.mm"
include "imim2i.mm"
include "com13.mm"
include "sylbid.mm"
include "com23.mm"
include "exp31.mm"
include "com25.mm"
include "com14.mm"
include "expdcom.mm"
include "mpid.mm"
include "impcom.mm"
include "mpd.mm"
include "imp.mm"

theorem nn0sumshdiglemA
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  let va: setvar a
  let vi: setvar i

  disjoint a k
  disjoint a x
  disjoint a y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint k x
  disjoint a i
  disjoint i k
  disjoint i x
  disjoint i y
  assert |- ( ( ( a e. NN /\ ( a / 2 ) e. NN ) /\ y e. NN ) -> ( A. x e. NN0 ( ( #b ` x ) = y -> x = sum_ k e. ( 0 ..^ y ) ( ( k ( digit ` 2 ) x ) x. ( 2 ^ k ) ) ) -> ( ( #b ` a ) = ( y + 1 ) -> a = sum_ k e. ( 0 ..^ ( y + 1 ) ) ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) )

  proof
    va
    cv
    #
    cn
    wcel
    #
    @0
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wa
    #
    vy
    cv
    #
    cn
    wcel
    #
    vx
    cv
    #
    cblen
    cfv
    #
    @5
    wceq
    #
    @7
    cc0
    @5
    cfzo
    co
    #
    vk
    cv
    #
    @7
    c2
    cdig
    cfv
    #
    co
    #
    c2
    @11
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @0
    cblen
    cfv
    #
    @5
    c1
    caddc
    co
    #
    wceq
    #
    @0
    cc0
    @21
    cfzo
    co
    #
    @11
    @0
    @12
    co
    #
    @14
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    wi
    #
    @4
    @2
    cblen
    cfv
    #
    @20
    c1
    cmin
    co
    #
    wceq
    #
    @6
    @29
    wi
    #
    @3
    @1
    @2
    cn0
    wcel
    #
    @32
    @2
    nnnn0
    #
    @0
    blennn0em1
    sylan2
    @3
    @1
    @32
    @33
    wi
    #
    @3
    @1
    @34
    @36
    @35
    @34
    @3
    @1
    @36
    @34
    @19
    @32
    @6
    @3
    @1
    wa
    #
    @28
    @34
    @19
    @32
    @6
    @37
    @28
    wi
    wi
    wi
    #
    @34
    @19
    wa
    @30
    @5
    wceq
    #
    @2
    @10
    @11
    @2
    @12
    co
    #
    @14
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    @38
    @18
    @44
    vx
    @2
    cn0
    @7
    @2
    wceq
    #
    @9
    @39
    @17
    @43
    @45
    @8
    @30
    @5
    @7
    @2
    cblen
    fveq2
    eqeq1d
    @45
    @7
    @2
    @16
    @42
    @45
    id
    @45
    @10
    @15
    @41
    vk
    @45
    @15
    @41
    wceq
    @11
    @10
    wcel
    @45
    @13
    @40
    @14
    cmul
    @7
    @2
    @11
    @12
    oveq2
    oveq1d
    adantr
    sumeq2dv
    eqeq12d
    imbi12d
    rspcva
    @37
    @32
    @6
    @44
    @28
    @37
    @22
    @6
    @44
    @32
    @27
    @37
    @22
    @6
    @44
    @32
    @27
    wi
    wi
    @37
    @22
    wa
    #
    @6
    wa
    #
    @32
    @44
    @27
    @47
    @32
    @39
    @44
    @27
    wi
    @47
    @31
    @5
    @30
    @46
    @6
    @31
    @21
    c1
    cmin
    co
    #
    @5
    @46
    @20
    @21
    c1
    cmin
    @37
    @22
    simpr
    oveq1d
    @6
    @5
    cc
    wcel
    @48
    @5
    wceq
    @5
    nncn
    @5
    pncan1
    syl
    sylan9eq
    eqeq2d
    @44
    @39
    @47
    @27
    @43
    @47
    @27
    wi
    @39
    @43
    @47
    @27
    @43
    @47
    wa
    #
    @26
    @10
    vi
    cv
    #
    @2
    @12
    co
    #
    c2
    @50
    cexp
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    c2
    cmul
    co
    #
    @2
    c2
    cmul
    co
    #
    @0
    @47
    @26
    @55
    wceq
    @43
    @47
    @26
    cc0
    @5
    cfz
    co
    #
    @25
    vk
    csu
    cc0
    @0
    @12
    co
    #
    c1
    cmul
    co
    #
    cc0
    c1
    caddc
    co
    #
    @5
    cfz
    co
    #
    @25
    vk
    csu
    #
    caddc
    co
    #
    @55
    @47
    @23
    @57
    @25
    vk
    @47
    @57
    @23
    @47
    @5
    cz
    wcel
    #
    @57
    @23
    wceq
    @6
    @64
    @46
    @5
    nnz
    #
    adantl
    #
    cc0
    @5
    fzval3
    syl
    eqcomd
    sumeq1d
    @47
    @25
    @59
    vk
    cc0
    @5
    @6
    @5
    cc0
    cuz
    cfv
    wcel
    #
    @46
    @6
    @5
    cn0
    wcel
    @67
    @5
    nnnn0
    @5
    elnn0uz
    sylib
    adantl
    @47
    @11
    @57
    wcel
    #
    wa
    #
    @24
    @14
    @69
    @24
    @69
    c2
    cn
    wcel
    #
    @11
    cz
    wcel
    #
    @0
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @24
    cn0
    wcel
    #
    @70
    @69
    2nn
    a1i
    @68
    @71
    @47
    @11
    cc0
    @5
    elfzelz
    adantl
    @1
    @73
    @3
    @22
    @6
    @68
    @1
    @0
    cn0
    wcel
    #
    @73
    @0
    nnnn0
    #
    @0
    nn0rp0
    syl
    #
    ad4antlr
    c2
    @0
    @11
    digvalnn0
    #
    syl3anc
    nn0cnd
    @68
    @14
    cc
    wcel
    #
    @47
    @68
    @14
    @68
    c2
    @11
    c2
    cn0
    wcel
    #
    @68
    2nn0
    a1i
    @11
    @5
    elfznn0
    nn0expcld
    nn0cnd
    adantl
    mulcld
    @11
    cc0
    wceq
    #
    @25
    @58
    c2
    cc0
    cexp
    co
    #
    cmul
    co
    @59
    @81
    @24
    @58
    @14
    @82
    cmul
    @11
    cc0
    @0
    @12
    oveq1
    @11
    cc0
    c2
    cexp
    oveq2
    oveq12d
    @82
    c1
    @58
    cmul
    c2
    cc
    wcel
    #
    @82
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    oveq2i
    syl6eq
    fsum1p
    @47
    @63
    cc0
    @60
    c1
    cmin
    co
    #
    @5
    c1
    cmin
    co
    #
    cfz
    co
    #
    @50
    c1
    caddc
    co
    #
    @0
    @12
    co
    #
    c2
    @87
    cexp
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    caddc
    co
    #
    @55
    @47
    @59
    cc0
    @62
    @91
    caddc
    @46
    @59
    cc0
    wceq
    #
    @6
    @37
    @93
    @22
    @37
    @59
    cc0
    c1
    cmul
    co
    #
    cc0
    @37
    @58
    cc0
    c1
    cmul
    @1
    @75
    @34
    @58
    cc0
    wceq
    @3
    @76
    @35
    @0
    0dig2nn0e
    syl2anr
    oveq1d
    c1
    cr
    wcel
    @94
    cc0
    wceq
    1re
    c1
    mul02lem2
    ax-mp
    syl6eq
    adantr
    adantr
    @47
    @25
    @90
    vk
    vi
    c1
    @60
    @5
    c1
    cz
    wcel
    @47
    1z
    a1i
    @60
    cz
    wcel
    @47
    @60
    c1
    cz
    0p1e1
    1z
    eqeltri
    a1i
    @66
    @47
    @11
    @61
    wcel
    #
    wa
    #
    @24
    @14
    @96
    @24
    @96
    @70
    @71
    @73
    @74
    @70
    @96
    2nn
    a1i
    @95
    @71
    @47
    @11
    @60
    @5
    elfzelz
    adantl
    @1
    @73
    @3
    @22
    @6
    @95
    @77
    ad4antlr
    @78
    syl3anc
    nn0cnd
    @95
    @79
    @47
    @95
    c2
    @11
    @95
    2cnd
    @11
    cn0
    wcel
    @11
    c1
    @5
    cfz
    co
    #
    @61
    @11
    @97
    wcel
    @11
    @11
    @5
    elfznn
    nnnn0d
    @60
    c1
    @5
    cfz
    0p1e1
    oveq1i
    eleq2s
    expcld
    adantl
    mulcld
    @11
    @87
    wceq
    @24
    @88
    @14
    @89
    cmul
    @11
    @87
    @0
    @12
    oveq1
    @11
    @87
    c2
    cexp
    oveq2
    oveq12d
    fsumshftm
    oveq12d
    @47
    @10
    @90
    vi
    csu
    #
    @10
    @53
    c2
    cmul
    co
    #
    vi
    csu
    @92
    @55
    @47
    @10
    @90
    @99
    vi
    @47
    @50
    @10
    wcel
    #
    wa
    #
    @90
    @51
    @52
    c2
    cmul
    co
    #
    cmul
    co
    #
    @99
    @101
    @88
    @51
    @89
    @102
    cmul
    @101
    @34
    @75
    @50
    cn0
    wcel
    #
    @88
    @51
    wceq
    @3
    @34
    @1
    @22
    @6
    @100
    @35
    ad4antr
    @1
    @75
    @3
    @22
    @6
    @100
    @76
    ad4antlr
    @100
    @104
    @47
    @50
    @5
    elfzonn0
    #
    adantl
    @0
    @50
    dignn0ehalf
    syl3anc
    @100
    @89
    @102
    wceq
    @47
    @100
    c2
    @50
    @100
    2cnd
    @105
    expp1d
    adantl
    oveq12d
    @101
    @51
    cc
    wcel
    #
    @52
    cc
    wcel
    #
    @83
    @103
    @99
    wceq
    @101
    @51
    @101
    @70
    @50
    cz
    wcel
    #
    @2
    @72
    wcel
    #
    @51
    cn0
    wcel
    @70
    @101
    2nn
    a1i
    #
    @100
    @108
    @47
    @50
    cc0
    @5
    elfzoelz
    #
    adantl
    @3
    @109
    @1
    @22
    @6
    @100
    @3
    @34
    @109
    @35
    @2
    nn0rp0
    syl
    ad4antr
    c2
    @2
    @50
    digvalnn0
    syl3anc
    nn0cnd
    #
    @100
    @107
    @47
    @100
    @52
    @100
    c2
    @50
    c2
    cr
    wcel
    @100
    2re
    a1i
    @105
    reexpcld
    recnd
    adantl
    @101
    2cnd
    @106
    @107
    @83
    w3a
    @99
    @103
    @51
    @52
    c2
    mulass
    eqcomd
    syl3anc
    eqtrd
    sumeq2dv
    @47
    @92
    cc0
    @98
    caddc
    co
    @98
    @47
    @91
    @98
    cc0
    caddc
    @47
    @86
    @10
    @90
    vi
    @6
    @86
    @10
    wceq
    @46
    @6
    @86
    cc0
    @85
    cfz
    co
    #
    @10
    @6
    @84
    cc0
    @85
    cfz
    @84
    cc0
    wceq
    #
    @6
    cc0
    cc
    wcel
    @114
    0cn
    cc0
    pncan1
    ax-mp
    a1i
    oveq1d
    @6
    @64
    @113
    @10
    wceq
    @65
    @64
    @10
    @113
    cc0
    @5
    fzoval
    eqcomd
    syl
    eqtrd
    adantl
    sumeq1d
    oveq2d
    @47
    @98
    @47
    @10
    @90
    vi
    @10
    cfn
    wcel
    @47
    cc0
    @5
    fzofi
    a1i
    #
    @101
    @88
    @89
    @101
    @88
    @101
    @70
    @87
    cz
    wcel
    #
    @73
    @88
    cn0
    wcel
    @110
    @100
    @116
    @47
    @100
    @50
    @111
    peano2zd
    adantl
    @1
    @73
    @3
    @22
    @6
    @100
    @77
    ad4antlr
    c2
    @0
    @87
    digvalnn0
    syl3anc
    nn0cnd
    @100
    @89
    cc
    wcel
    @47
    @100
    @89
    @100
    c2
    @87
    @80
    @100
    2nn0
    a1i
    #
    @100
    @104
    @87
    cn0
    wcel
    @105
    @50
    peano2nn0
    syl
    nn0expcld
    nn0cnd
    adantl
    mulcld
    fsumcl
    addid2d
    eqtrd
    @47
    @10
    @53
    c2
    vi
    @115
    @47
    2cnd
    @101
    @51
    @52
    @112
    @100
    @107
    @47
    @100
    @52
    @100
    c2
    @50
    @117
    @105
    nn0expcld
    nn0cnd
    adantl
    mulcld
    fsummulc1
    3eqtr4d
    eqtrd
    3eqtrd
    adantl
    @49
    @54
    @2
    c2
    cmul
    @49
    @2
    @54
    @47
    @43
    @2
    @54
    wceq
    @47
    @42
    @54
    @2
    @42
    @54
    wceq
    @47
    @10
    @41
    @53
    vk
    vi
    vk
    vi
    weq
    @40
    @51
    @14
    @52
    cmul
    @11
    @50
    @2
    @12
    oveq1
    @11
    @50
    c2
    cexp
    oveq2
    oveq12d
    cbvsumv
    a1i
    eqeq2d
    biimpac
    eqcomd
    oveq1d
    @47
    @56
    @0
    wceq
    #
    @43
    @1
    @118
    @3
    @22
    @6
    @1
    @0
    c2
    @0
    nncn
    @1
    2cnd
    c2
    cc0
    wne
    @1
    2ne0
    a1i
    divcan1d
    ad3antlr
    adantl
    3eqtrrd
    ex
    imim2i
    com13
    sylbid
    com23
    exp31
    com25
    com14
    syl
    ex
    com25
    expdcom
    mpid
    impcom
    mpd
    imp
end
