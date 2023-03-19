include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cn0.mm"
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
include "wral.mm"
include "caddc.mm"
include "cuz.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "wa.mm"
include "1t1e1.mm"
include "eqcomi.mm"
include "simpl.mm"
include "csn.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "fveq2.mm"
include "blen1.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "fzo01.mm"
include "sylan9eqr.mm"
include "sumeq1d.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "cvv.mm"
include "cc.mm"
include "c0ex.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "oveq1.mm"
include "cpr.mm"
include "1ex.mm"
include "prid2.mm"
include "0dig2pr01.mm"
include "ax-mp.mm"
include "2cn.mm"
include "exp0.mm"
include "oveq12d.mm"
include "sumsn.mm"
include "mp2an.mm"
include "adantr.mm"
include "eqtrd.mm"
include "3eqtr4a.mm"
include "ex.mm"
include "a1d.mm"
include "2a1d.mm"
include "wb.mm"
include "eluzge2nn0.mm"
include "nn0ob.mm"
include "bicomd.mm"
include "syl.mm"
include "blennngt2o2.mm"
include "sylbid.mm"
include "imp.mm"
include "eqeq1d.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "eqeq1.mm"
include "nncn.mm"
include "ad2antll.mm"
include "blennn0elnn.mm"
include "nncnd.mm"
include "ad2antrl.mm"
include "1cnd.mm"
include "addcan2d.mm"
include "eqcom.mm"
include "cfz.mm"
include "cz.mm"
include "nnz.mm"
include "fzval3.mm"
include "eqcomd.mm"
include "nnnn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "cpnf.mm"
include "cico.mm"
include "2nn.mm"
include "a1i.mm"
include "elfzelz.mm"
include "adantl.mm"
include "nn0rp0.mm"
include "digvalnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "2nn0.mm"
include "elfznn0.mm"
include "nn0expcld.mm"
include "mulcld.mm"
include "oveq2i.mm"
include "fsum1p.mm"
include "biimparc.mm"
include "0dig2nn0o.mm"
include "syl2anc.mm"
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
include "3eqtrd.mm"
include "elfzoelz.mm"
include "elfzonn0.mm"
include "mulassd.mm"
include "sumeq2dv.mm"
include "0cn.mm"
include "pncan1.mm"
include "fzoval.mm"
include "eqtr4d.mm"
include "cfl.mm"
include "simprlr.mm"
include "dignn0flhalf.mm"
include "syl2an.mm"
include "eluzelz.mm"
include "nn0z.mm"
include "zob.mm"
include "syl5ibr.mm"
include "jca.mm"
include "ancoms.mm"
include "zofldiv2.mm"
include "expp1d.mm"
include "sumeq12dv.mm"
include "weq.mm"
include "cbvsumv.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "cfn.mm"
include "fzofi.mm"
include "fsummulc1.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "w3a.mm"
include "eluzelcn.mm"
include "peano2cnm.mm"
include "2ne0.mm"
include "3jca.mm"
include "divcan1.mm"
include "pncan3.mm"
include "3eqtrrd.mm"
include "imim2i.mm"
include "com13.mm"
include "syl5bi.mm"
include "com23.mm"
include "com14.mm"
include "exp4c.mm"
include "com35.mm"
include "pm2.43a.mm"
include "com25.mm"
include "impcom.mm"
include "mpd.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp31.mm"

theorem nn0sumshdiglemB
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
  assert |- ( ( ( a e. NN /\ ( ( a - 1 ) / 2 ) e. NN0 ) /\ y e. NN ) -> ( A. x e. NN0 ( ( #b ` x ) = y -> x = sum_ k e. ( 0 ..^ y ) ( ( k ( digit ` 2 ) x ) x. ( 2 ^ k ) ) ) -> ( ( #b ` a ) = ( y + 1 ) -> a = sum_ k e. ( 0 ..^ ( y + 1 ) ) ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) )

  proof
    va
    cv
    #
    cn
    wcel
    #
    @0
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cn0
    wcel
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
    @1
    @0
    c1
    wceq
    #
    @0
    c2
    cuz
    cfv
    wcel
    #
    wo
    @4
    @6
    @29
    wi
    #
    wi
    #
    @0
    elnn1uz2
    @30
    @33
    @31
    @30
    @29
    @4
    @6
    @30
    @28
    @19
    @30
    @22
    @27
    @30
    @22
    wa
    #
    c1
    c1
    c1
    cmul
    co
    #
    @0
    @26
    @35
    c1
    1t1e1
    eqcomi
    @30
    @22
    simpl
    @34
    @26
    cc0
    csn
    #
    @25
    vk
    csu
    #
    @35
    @34
    @23
    @36
    @25
    vk
    @22
    @30
    @23
    cc0
    @20
    cfzo
    co
    #
    @36
    @23
    @38
    wceq
    @21
    @20
    @21
    @20
    cc0
    cfzo
    oveq2
    eqcoms
    @30
    @38
    cc0
    c1
    cfzo
    co
    @36
    @30
    @20
    c1
    cc0
    cfzo
    @30
    @20
    c1
    cblen
    cfv
    c1
    @0
    c1
    cblen
    fveq2
    blen1
    syl6eq
    oveq2d
    fzo01
    syl6eq
    sylan9eqr
    sumeq1d
    @30
    @37
    @35
    wceq
    @22
    @30
    @37
    @36
    @11
    c1
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
    @35
    @30
    @36
    @25
    @40
    vk
    @30
    @24
    @39
    @14
    cmul
    @0
    c1
    @11
    @12
    oveq2
    oveq1d
    sumeq2sdv
    cc0
    cvv
    wcel
    @35
    cc
    wcel
    @41
    @35
    wceq
    c0ex
    c1
    c1
    ax-1cn
    ax-1cn
    mulcli
    @40
    @35
    vk
    cc0
    cvv
    @11
    cc0
    wceq
    #
    @39
    c1
    @14
    c1
    cmul
    @42
    @39
    cc0
    c1
    @12
    co
    #
    c1
    @11
    cc0
    c1
    @12
    oveq1
    c1
    cc0
    c1
    cpr
    wcel
    @43
    c1
    wceq
    cc0
    c1
    1ex
    prid2
    c1
    0dig2pr01
    ax-mp
    syl6eq
    @42
    @14
    c2
    cc0
    cexp
    co
    #
    c1
    @11
    cc0
    c2
    cexp
    oveq2
    #
    c2
    cc
    wcel
    #
    @44
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    #
    syl6eq
    oveq12d
    sumsn
    mp2an
    syl6eq
    adantr
    eqtrd
    3eqtr4a
    ex
    a1d
    2a1d
    @31
    @4
    @32
    @31
    @4
    wa
    #
    @20
    @3
    cblen
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @32
    @31
    @4
    @51
    @31
    @4
    @0
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @51
    @31
    @0
    cn0
    wcel
    #
    @4
    @53
    wb
    @0
    eluzge2nn0
    #
    @54
    @53
    @4
    @0
    nn0ob
    #
    bicomd
    syl
    @31
    @53
    @51
    @0
    blennngt2o2
    ex
    sylbid
    imp
    @4
    @31
    @51
    @32
    wi
    @4
    @19
    @51
    @6
    @31
    @28
    @19
    @4
    @51
    @6
    @31
    @28
    wi
    wi
    wi
    #
    @4
    @19
    @4
    @57
    wi
    #
    @4
    @19
    wa
    @49
    @5
    wceq
    #
    @3
    @10
    @11
    @3
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
    @58
    @18
    @64
    vx
    @3
    cn0
    @7
    @3
    wceq
    #
    @9
    @59
    @17
    @63
    @65
    @8
    @49
    @5
    @7
    @3
    cblen
    fveq2
    eqeq1d
    @65
    @7
    @3
    @16
    @62
    @65
    id
    @65
    @10
    @15
    @61
    vk
    @65
    @13
    @60
    @14
    cmul
    @7
    @3
    @11
    @12
    oveq2
    oveq1d
    sumeq2sdv
    eqeq12d
    imbi12d
    rspcva
    @64
    @4
    @31
    @6
    @51
    @28
    @64
    @4
    @31
    @6
    @51
    @28
    wi
    @22
    @4
    @31
    wa
    #
    @6
    wa
    #
    @51
    @64
    @27
    @22
    @51
    @67
    @64
    @27
    wi
    #
    @22
    @51
    @21
    @50
    wceq
    #
    @67
    @68
    wi
    @20
    @21
    @50
    eqeq1
    @22
    @67
    @69
    @68
    @22
    @67
    @69
    @68
    wi
    @22
    @67
    wa
    #
    @69
    @5
    @49
    wceq
    #
    @68
    @70
    @5
    @49
    c1
    @6
    @5
    cc
    wcel
    @22
    @66
    @5
    nncn
    ad2antll
    @66
    @49
    cc
    wcel
    #
    @22
    @6
    @4
    @72
    @31
    @4
    @49
    @3
    blennn0elnn
    nncnd
    adantr
    ad2antrl
    @70
    1cnd
    addcan2d
    @71
    @59
    @70
    @68
    @5
    @49
    eqcom
    @64
    @59
    @70
    @27
    @63
    @70
    @27
    wi
    @59
    @63
    @70
    @27
    @63
    @70
    wa
    #
    @26
    c1
    cc0
    c1
    caddc
    co
    #
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
    vi
    cv
    #
    c1
    caddc
    co
    #
    @0
    @12
    co
    #
    c2
    @79
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
    c1
    @3
    c2
    cmul
    co
    #
    caddc
    co
    #
    @0
    @70
    @26
    @84
    wceq
    @63
    @70
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
    @74
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
    @84
    @70
    @23
    @87
    @25
    vk
    @70
    @87
    @23
    @70
    @5
    cz
    wcel
    #
    @87
    @23
    wceq
    @6
    @92
    @22
    @66
    @5
    nnz
    #
    ad2antll
    #
    cc0
    @5
    fzval3
    syl
    eqcomd
    sumeq1d
    @70
    @25
    @89
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
    @22
    @66
    @6
    @5
    cn0
    wcel
    @95
    @5
    nnnn0
    @5
    elnn0uz
    sylib
    ad2antll
    @70
    @11
    @87
    wcel
    #
    wa
    #
    @24
    @14
    @97
    @24
    @70
    @96
    @24
    cn0
    wcel
    #
    @66
    @96
    @98
    wi
    @22
    @6
    @66
    @96
    @98
    @66
    @96
    wa
    #
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
    @98
    @100
    @99
    2nn
    a1i
    @96
    @101
    @66
    @11
    cc0
    @5
    elfzelz
    adantl
    @66
    @103
    @96
    @31
    @103
    @4
    @31
    @54
    @103
    @55
    @0
    nn0rp0
    #
    syl
    adantl
    adantr
    c2
    @0
    @11
    digvalnn0
    #
    syl3anc
    ex
    ad2antrl
    imp
    nn0cnd
    @96
    @14
    cc
    wcel
    #
    @70
    @96
    @14
    @96
    c2
    @11
    c2
    cn0
    wcel
    #
    @96
    2nn0
    a1i
    @11
    @5
    elfznn0
    nn0expcld
    nn0cnd
    adantl
    mulcld
    @42
    @25
    @88
    @44
    cmul
    co
    @89
    @42
    @24
    @88
    @14
    @44
    cmul
    @11
    cc0
    @0
    @12
    oveq1
    @45
    oveq12d
    @44
    c1
    @88
    cmul
    @47
    oveq2i
    syl6eq
    fsum1p
    @70
    @89
    c1
    @91
    @83
    caddc
    @70
    @89
    @35
    c1
    @70
    @88
    c1
    c1
    cmul
    @66
    @88
    c1
    wceq
    #
    @22
    @6
    @66
    @54
    @53
    @108
    @31
    @54
    @4
    @55
    adantl
    @31
    @53
    @4
    @31
    @54
    @53
    @4
    wb
    @55
    @56
    syl
    biimparc
    @0
    0dig2nn0o
    syl2anc
    ad2antrl
    oveq1d
    1t1e1
    syl6eq
    @70
    @25
    @82
    vk
    vi
    c1
    @74
    @5
    c1
    cz
    wcel
    @70
    1z
    a1i
    @74
    cz
    wcel
    @70
    @74
    c1
    cz
    0p1e1
    1z
    eqeltri
    a1i
    @94
    @70
    @11
    @90
    wcel
    #
    wa
    #
    @24
    @14
    @110
    @24
    @70
    @109
    @98
    @66
    @109
    @98
    wi
    #
    @22
    @6
    @31
    @111
    @4
    @31
    @109
    @98
    @31
    @109
    wa
    #
    @100
    @101
    @103
    @98
    @100
    @112
    2nn
    a1i
    @109
    @101
    @31
    @11
    @74
    @5
    elfzelz
    adantl
    @112
    @54
    @103
    @31
    @54
    @109
    @55
    adantr
    @104
    syl
    @105
    syl3anc
    ex
    adantl
    ad2antrl
    imp
    nn0cnd
    @109
    @106
    @70
    @109
    c2
    @11
    @109
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
    @90
    @11
    @113
    wcel
    @11
    @11
    @5
    elfznn
    nnnn0d
    @74
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
    @79
    wceq
    @24
    @80
    @14
    @81
    cmul
    @11
    @79
    @0
    @12
    oveq1
    @11
    @79
    c2
    cexp
    oveq2
    oveq12d
    fsumshftm
    oveq12d
    3eqtrd
    adantl
    @73
    @83
    @85
    c1
    caddc
    @73
    @10
    @78
    @3
    @12
    co
    #
    c2
    @78
    cexp
    co
    #
    c2
    cmul
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    @10
    @114
    @115
    cmul
    co
    #
    c2
    cmul
    co
    #
    vi
    csu
    #
    @83
    @85
    @70
    @118
    @121
    wceq
    @63
    @70
    @10
    @117
    @120
    vi
    @70
    @78
    @10
    wcel
    #
    wa
    #
    @120
    @117
    @123
    @114
    @115
    c2
    @70
    @122
    @114
    cc
    wcel
    #
    @66
    @122
    @124
    wi
    @22
    @6
    @66
    @122
    @124
    @66
    @122
    wa
    #
    @114
    @125
    @100
    @78
    cz
    wcel
    #
    @3
    @102
    wcel
    #
    @114
    cn0
    wcel
    @100
    @125
    2nn
    a1i
    @122
    @126
    @66
    @78
    cc0
    @5
    elfzoelz
    adantl
    @66
    @127
    @122
    @4
    @127
    @31
    @3
    nn0rp0
    adantr
    adantr
    c2
    @3
    @78
    digvalnn0
    syl3anc
    nn0cnd
    #
    ex
    ad2antrl
    imp
    @122
    @115
    cc
    wcel
    #
    @70
    @122
    @115
    @122
    c2
    @78
    @107
    @122
    2nn0
    a1i
    @78
    @5
    elfzonn0
    nn0expcld
    nn0cnd
    #
    adantl
    @123
    2cnd
    mulassd
    eqcomd
    sumeq2dv
    adantl
    @70
    @83
    @118
    wceq
    @63
    @70
    @77
    @10
    @82
    @117
    vi
    @6
    @77
    @10
    wceq
    @22
    @66
    @6
    @77
    cc0
    @76
    cfz
    co
    #
    @10
    @6
    @75
    cc0
    @76
    cfz
    @75
    cc0
    wceq
    #
    @6
    cc0
    cc
    wcel
    @132
    0cn
    cc0
    pncan1
    ax-mp
    #
    a1i
    oveq1d
    @6
    @92
    @10
    @131
    wceq
    @93
    cc0
    @5
    fzoval
    syl
    eqtr4d
    ad2antll
    @70
    @78
    @77
    wcel
    #
    wa
    #
    @80
    @114
    @81
    @116
    cmul
    @135
    @80
    @78
    @0
    c2
    cdiv
    co
    cfl
    cfv
    #
    @12
    co
    #
    @114
    @70
    @31
    @78
    cn0
    wcel
    #
    @80
    @137
    wceq
    @134
    @22
    @4
    @31
    @6
    simprlr
    @138
    @78
    @131
    @77
    @78
    @76
    elfznn0
    @75
    cc0
    @76
    cfz
    @133
    oveq1i
    eleq2s
    #
    @0
    @78
    dignn0flhalf
    syl2an
    @135
    @136
    @3
    @78
    @12
    @135
    @0
    cz
    wcel
    #
    @52
    cz
    wcel
    #
    wa
    #
    @136
    @3
    wceq
    @70
    @142
    @134
    @66
    @142
    @22
    @6
    @31
    @4
    @142
    @48
    @140
    @141
    @31
    @140
    @4
    c2
    @0
    eluzelz
    #
    adantr
    @31
    @4
    @141
    @4
    @141
    @31
    @3
    cz
    wcel
    #
    @3
    nn0z
    @31
    @140
    @141
    @144
    wb
    @143
    @0
    zob
    syl
    syl5ibr
    imp
    jca
    ancoms
    ad2antrl
    adantr
    @0
    zofldiv2
    syl
    oveq2d
    eqtrd
    @134
    @81
    @116
    wceq
    @70
    @134
    c2
    @78
    @134
    2cnd
    @139
    expp1d
    adantl
    oveq12d
    sumeq12dv
    adantl
    @73
    @85
    @10
    @119
    vi
    csu
    #
    c2
    cmul
    co
    @121
    @73
    @3
    @145
    c2
    cmul
    @63
    @3
    @145
    wceq
    #
    @70
    @63
    @146
    @62
    @145
    @3
    @10
    @61
    @119
    vk
    vi
    vk
    vi
    weq
    @60
    @114
    @14
    @115
    cmul
    @11
    @78
    @3
    @12
    oveq1
    @11
    @78
    c2
    cexp
    oveq2
    oveq12d
    cbvsumv
    eqeq2i
    biimpi
    adantr
    oveq1d
    @73
    @10
    @119
    c2
    vi
    @10
    cfn
    wcel
    @73
    cc0
    @5
    fzofi
    a1i
    @73
    2cnd
    @73
    @122
    @119
    cc
    wcel
    #
    @67
    @122
    @147
    wi
    #
    @63
    @22
    @66
    @148
    @6
    @66
    @122
    @147
    @125
    @114
    @115
    @128
    @122
    @129
    @66
    @130
    adantl
    mulcld
    ex
    adantr
    ad2antll
    imp
    fsummulc1
    eqtrd
    3eqtr4d
    oveq2d
    @67
    @86
    @0
    wceq
    #
    @63
    @22
    @66
    @149
    @6
    @66
    @86
    c1
    @2
    caddc
    co
    #
    @0
    @66
    @85
    @2
    c1
    caddc
    @66
    @2
    cc
    wcel
    #
    @46
    c2
    cc0
    wne
    #
    w3a
    #
    @85
    @2
    wceq
    @31
    @153
    @4
    @31
    @151
    @46
    @152
    @31
    @0
    cc
    wcel
    #
    @151
    c2
    @0
    eluzelcn
    #
    @0
    peano2cnm
    syl
    @31
    2cnd
    @152
    @31
    2ne0
    a1i
    3jca
    adantl
    @2
    c2
    divcan1
    syl
    oveq2d
    @66
    c1
    cc
    wcel
    #
    @154
    wa
    #
    @150
    @0
    wceq
    @31
    @157
    @4
    @31
    @156
    @154
    @31
    1cnd
    @155
    jca
    adantl
    c1
    @0
    pncan3
    syl
    eqtrd
    adantr
    ad2antll
    3eqtrrd
    ex
    imim2i
    com13
    syl5bi
    sylbid
    ex
    com23
    sylbid
    com23
    com14
    exp4c
    com35
    syl
    ex
    pm2.43a
    com25
    impcom
    mpd
    ex
    jaoi
    sylbi
    imp31
end
