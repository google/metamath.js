include "cfn.mm"
include "wcel.mm"
include "cvol.mm"
include "cdm.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "wral.mm"
include "wdisj.mm"
include "ciun.mm"
include "csu.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "raleq.mm"
include "disjeq1.mm"
include "anbi12d.mm"
include "iuneq1.mm"
include "fveq2d.mm"
include "sumeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "weq.mm"
include "cc0.mm"
include "covol.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovol0.mm"
include "eqtri.mm"
include "0iun.mm"
include "fveq2i.mm"
include "sum0.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "wn.mm"
include "wss.mm"
include "ssun1.mm"
include "ssralv.mm"
include "disjss1.mm"
include "anim12i.mm"
include "imim1i.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "oveq1.mm"
include "iunxun.mm"
include "vex.mm"
include "csbeq1.mm"
include "iunxsn.mm"
include "uneq2i.mm"
include "cin.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "simpll.mm"
include "simprl.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "mpsyl.mm"
include "finiunmbl.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "nfel1.mm"
include "nffv.mm"
include "nfan.mm"
include "eleq1d.mm"
include "rspc.mm"
include "simpld.mm"
include "simplr.mm"
include "elin.mm"
include "wrex.mm"
include "eliun.mm"
include "w3a.mm"
include "simplrr.mm"
include "cbvdisj.mm"
include "sylib.mm"
include "simpr1.mm"
include "elun1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "disji.mm"
include "syl122anc.mm"
include "eqeltrrd.mm"
include "3exp2.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "impd.mm"
include "mtod.mm"
include "eq0rdv.mm"
include "cle.mm"
include "wbr.mm"
include "nfv.mm"
include "cbvral.mm"
include "r19.21bi.mm"
include "mblss.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "biimpa.mm"
include "fsumrecl.mm"
include "adantr.mm"
include "jca.mm"
include "ovolfiniun.mm"
include "ovollecl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "simprd.mm"
include "volun.mm"
include "syl32anc.mm"
include "syl5eq.mm"
include "disjsn.mm"
include "eqidd.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "cvv.mm"
include "cc.mm"
include "sumsn.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "cbvsumi.mm"
include "eqeq12i.mm"
include "3imtr4g.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "findcard2s.mm"
include "3impib.mm"

theorem volfiniun
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A k
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m w
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B m
  disjoint B n
  disjoint B w
  disjoint B y
  disjoint B z
  assert |- ( ( A e. Fin /\ A. k e. A ( B e. dom vol /\ ( vol ` B ) e. RR ) /\ Disj_ k e. A B ) -> ( vol ` U_ k e. A B ) = sum_ k e. A ( vol ` B ) )

  proof
    cA
    cfn
    wcel
    cB
    cvol
    cdm
    #
    wcel
    #
    cB
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vk
    cA
    wral
    #
    vk
    cA
    cB
    wdisj
    #
    vk
    cA
    cB
    ciun
    #
    cvol
    cfv
    #
    cA
    @2
    vk
    csu
    #
    wceq
    #
    @4
    vk
    vw
    cv
    #
    wral
    #
    vk
    @11
    cB
    wdisj
    #
    wa
    #
    vk
    @11
    cB
    ciun
    #
    cvol
    cfv
    #
    @11
    @2
    vk
    csu
    #
    wceq
    #
    wi
    @4
    vk
    c0
    wral
    #
    vk
    c0
    cB
    wdisj
    #
    wa
    #
    vk
    c0
    cB
    ciun
    #
    cvol
    cfv
    #
    c0
    @2
    vk
    csu
    #
    wceq
    #
    wi
    @4
    vk
    vy
    cv
    #
    wral
    #
    vk
    @26
    cB
    wdisj
    #
    wa
    #
    vk
    @26
    cB
    ciun
    #
    cvol
    cfv
    #
    @26
    @2
    vk
    csu
    #
    wceq
    #
    wi
    #
    @4
    vk
    @26
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    vk
    @37
    cB
    wdisj
    #
    wa
    #
    vk
    @37
    cB
    ciun
    #
    cvol
    cfv
    #
    @37
    @2
    vk
    csu
    #
    wceq
    #
    wi
    #
    @5
    @6
    wa
    #
    @10
    wi
    vw
    vy
    vz
    cA
    @11
    c0
    wceq
    #
    @14
    @21
    @18
    @25
    @47
    @12
    @19
    @13
    @20
    @4
    vk
    @11
    c0
    raleq
    vk
    @11
    c0
    cB
    disjeq1
    anbi12d
    @47
    @16
    @23
    @17
    @24
    @47
    @15
    @22
    cvol
    vk
    @11
    c0
    cB
    iuneq1
    fveq2d
    @11
    c0
    @2
    vk
    sumeq1
    eqeq12d
    imbi12d
    vw
    vy
    weq
    #
    @14
    @29
    @18
    @33
    @48
    @12
    @27
    @13
    @28
    @4
    vk
    @11
    @26
    raleq
    vk
    @11
    @26
    cB
    disjeq1
    anbi12d
    @48
    @16
    @31
    @17
    @32
    @48
    @15
    @30
    cvol
    vk
    @11
    @26
    cB
    iuneq1
    fveq2d
    @11
    @26
    @2
    vk
    sumeq1
    eqeq12d
    imbi12d
    @11
    @37
    wceq
    #
    @14
    @40
    @18
    @44
    @49
    @12
    @38
    @13
    @39
    @4
    vk
    @11
    @37
    raleq
    vk
    @11
    @37
    cB
    disjeq1
    anbi12d
    @49
    @16
    @42
    @17
    @43
    @49
    @15
    @41
    cvol
    vk
    @11
    @37
    cB
    iuneq1
    fveq2d
    @11
    @37
    @2
    vk
    sumeq1
    eqeq12d
    imbi12d
    @11
    cA
    wceq
    #
    @14
    @46
    @18
    @10
    @50
    @12
    @5
    @13
    @6
    @4
    vk
    @11
    cA
    raleq
    vk
    @11
    cA
    cB
    disjeq1
    anbi12d
    @50
    @16
    @8
    @17
    @9
    @50
    @15
    @7
    cvol
    vk
    @11
    cA
    cB
    iuneq1
    fveq2d
    @11
    cA
    @2
    vk
    sumeq1
    eqeq12d
    imbi12d
    @25
    @21
    c0
    cvol
    cfv
    #
    cc0
    @23
    @24
    @51
    c0
    covol
    cfv
    #
    cc0
    c0
    @0
    wcel
    @51
    @52
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    @22
    c0
    cvol
    vk
    cB
    0iun
    fveq2i
    @2
    vk
    sum0
    3eqtr4i
    a1i
    @34
    @40
    @33
    wi
    @26
    cfn
    wcel
    #
    @35
    @26
    wcel
    #
    wn
    #
    wa
    #
    @45
    @40
    @29
    @33
    @38
    @27
    @39
    @28
    @26
    @37
    wss
    #
    @38
    @27
    wi
    @26
    @36
    ssun1
    #
    @4
    vk
    @26
    @37
    ssralv
    ax-mp
    @57
    @39
    @28
    wi
    @58
    vk
    @26
    @37
    cB
    disjss1
    ax-mp
    anim12i
    imim1i
    @56
    @40
    @33
    @44
    @56
    @40
    @33
    @44
    wi
    @56
    @40
    wa
    #
    vm
    @26
    vk
    vm
    cv
    #
    cB
    csb
    #
    ciun
    #
    cvol
    cfv
    #
    @26
    @61
    cvol
    cfv
    #
    vm
    csu
    #
    wceq
    #
    vm
    @37
    @61
    ciun
    #
    cvol
    cfv
    #
    @37
    @64
    vm
    csu
    #
    wceq
    #
    @33
    @44
    @66
    @70
    @59
    @63
    vk
    @35
    cB
    csb
    #
    cvol
    cfv
    #
    caddc
    co
    #
    @65
    @72
    caddc
    co
    #
    wceq
    @63
    @65
    @72
    caddc
    oveq1
    @59
    @68
    @73
    @69
    @74
    @59
    @68
    @62
    @71
    cun
    #
    cvol
    cfv
    #
    @73
    @67
    @75
    cvol
    @67
    @62
    vm
    @36
    @61
    ciun
    #
    cun
    @75
    vm
    @26
    @36
    @61
    iunxun
    @77
    @71
    @62
    vm
    @35
    @61
    @71
    vz
    vex
    #
    vk
    @60
    @35
    cB
    csbeq1
    #
    iunxsn
    uneq2i
    eqtri
    fveq2i
    @59
    @62
    @0
    wcel
    #
    @71
    @0
    wcel
    #
    @62
    @71
    cin
    #
    c0
    wceq
    @63
    cr
    wcel
    @72
    cr
    wcel
    #
    @76
    @73
    wceq
    @59
    @62
    @30
    @0
    vk
    vm
    @26
    cB
    @61
    vm
    cB
    nfcv
    #
    vk
    @60
    cB
    nfcsb1v
    #
    vk
    @60
    cB
    csbeq1a
    #
    cbviun
    #
    @59
    @53
    @1
    vk
    @26
    wral
    #
    @30
    @0
    wcel
    @53
    @55
    @40
    simpll
    #
    @57
    @59
    @1
    vk
    @37
    wral
    #
    @88
    @58
    @59
    @38
    @90
    @56
    @38
    @39
    simprl
    #
    @4
    @1
    vk
    @37
    @1
    @3
    simpl
    ralimi
    syl
    @1
    vk
    @26
    @37
    ssralv
    mpsyl
    @26
    cB
    vk
    finiunmbl
    syl2anc
    syl5eqelr
    #
    @59
    @81
    @83
    @35
    @37
    wcel
    #
    @59
    @38
    @81
    @83
    wa
    #
    @36
    @37
    @35
    @36
    @26
    ssun2
    vz
    vsnid
    sselii
    #
    @91
    @4
    @94
    vk
    @35
    @37
    @81
    @83
    vk
    vk
    @71
    @0
    vk
    @35
    cB
    nfcsb1v
    #
    nfel1
    vk
    @72
    cr
    vk
    @71
    cvol
    vk
    cvol
    nfcv
    #
    @96
    nffv
    nfel1
    nfan
    vk
    vz
    weq
    #
    @1
    @81
    @3
    @83
    @98
    cB
    @71
    @0
    vk
    @35
    cB
    csbeq1a
    #
    eleq1d
    @98
    @2
    @72
    cr
    @98
    cB
    @71
    cvol
    @99
    fveq2d
    eleq1d
    anbi12d
    rspc
    mpsyl
    #
    simpld
    @59
    vw
    @82
    @59
    @11
    @82
    wcel
    #
    @54
    @53
    @55
    @40
    simplr
    #
    @101
    @11
    @62
    wcel
    #
    @11
    @71
    wcel
    #
    wa
    @59
    @54
    @11
    @62
    @71
    elin
    @59
    @103
    @104
    @54
    @103
    @11
    @61
    wcel
    #
    vm
    @26
    wrex
    @59
    @104
    @54
    wi
    #
    vm
    @11
    @26
    @61
    eliun
    @59
    @105
    @106
    vm
    @26
    @59
    @60
    @26
    wcel
    #
    @105
    @104
    @54
    @59
    @107
    @105
    @104
    w3a
    #
    wa
    #
    @60
    @35
    @26
    @109
    vn
    @37
    vk
    vn
    cv
    #
    cB
    csb
    #
    wdisj
    #
    @60
    @37
    wcel
    #
    @93
    @105
    @104
    vm
    vz
    weq
    #
    @109
    @39
    @112
    @56
    @38
    @39
    @108
    simplrr
    vk
    vn
    @37
    cB
    @111
    vn
    cB
    nfcv
    vk
    @110
    cB
    nfcsb1v
    vk
    @110
    cB
    csbeq1a
    cbvdisj
    sylib
    @109
    @107
    @113
    @59
    @107
    @105
    @104
    simpr1
    #
    @60
    @26
    @36
    elun1
    #
    syl
    @93
    @109
    @95
    a1i
    @59
    @107
    @105
    @104
    simpr2
    @59
    @107
    @105
    @104
    simpr3
    vn
    @37
    @111
    @61
    @71
    @60
    @35
    @11
    vk
    @110
    @60
    cB
    csbeq1
    vk
    @110
    @35
    cB
    csbeq1
    disji
    syl122anc
    @115
    eqeltrrd
    3exp2
    rexlimdv
    syl5bi
    impd
    syl5bi
    mtod
    eq0rdv
    @59
    @63
    @62
    covol
    cfv
    #
    cr
    @59
    @80
    @63
    @117
    wceq
    @92
    @62
    mblvol
    syl
    @59
    @62
    cr
    wss
    #
    @26
    @61
    covol
    cfv
    #
    vm
    csu
    #
    cr
    wcel
    @117
    @120
    cle
    wbr
    #
    @117
    cr
    wcel
    @59
    @61
    cr
    wss
    #
    vm
    @26
    wral
    @118
    @59
    @122
    vm
    @26
    @107
    @59
    @113
    @122
    @116
    @59
    @113
    wa
    #
    @61
    @0
    wcel
    #
    @122
    @123
    @124
    @64
    cr
    wcel
    #
    @59
    @124
    @125
    wa
    #
    vm
    @37
    @59
    @38
    @126
    vm
    @37
    wral
    #
    @91
    @4
    @126
    vk
    vm
    @37
    @4
    vm
    nfv
    @124
    @125
    vk
    vk
    @61
    @0
    @85
    nfel1
    vk
    @64
    cr
    vk
    @61
    cvol
    @97
    @85
    nffv
    #
    nfel1
    nfan
    vk
    vm
    weq
    #
    @1
    @124
    @3
    @125
    @129
    cB
    @61
    @0
    @86
    eleq1d
    @129
    @2
    @64
    cr
    @129
    cB
    @61
    cvol
    @86
    fveq2d
    #
    eleq1d
    anbi12d
    cbvral
    sylib
    #
    r19.21bi
    #
    simpld
    @61
    mblss
    #
    syl
    sylan2
    ralrimiva
    vm
    @26
    @61
    cr
    iunss
    sylibr
    @59
    @26
    @119
    vm
    @89
    @107
    @59
    @113
    @119
    cr
    wcel
    #
    @116
    @123
    @126
    @134
    @132
    @124
    @125
    @134
    @124
    @64
    @119
    cr
    @61
    mblvol
    eleq1d
    biimpa
    #
    syl
    sylan2
    fsumrecl
    @59
    @53
    @122
    @134
    wa
    #
    vm
    @26
    wral
    #
    @121
    @89
    @57
    @59
    @136
    vm
    @37
    wral
    #
    @137
    @58
    @59
    @127
    @138
    @131
    @126
    @136
    vm
    @37
    @126
    @122
    @134
    @124
    @122
    @125
    @133
    adantr
    @135
    jca
    ralimi
    syl
    @136
    vm
    @26
    @37
    ssralv
    mpsyl
    @26
    @61
    vm
    ovolfiniun
    syl2anc
    @62
    @120
    ovollecl
    syl3anc
    eqeltrd
    @59
    @81
    @83
    @100
    simprd
    #
    @62
    @71
    volun
    syl32anc
    syl5eq
    @59
    @69
    @65
    @36
    @64
    vm
    csu
    #
    caddc
    co
    @74
    @59
    @26
    @36
    @64
    @37
    vm
    @59
    @55
    @26
    @36
    cin
    c0
    wceq
    @102
    @26
    @35
    disjsn
    sylibr
    @59
    @37
    eqidd
    @59
    @53
    @36
    cfn
    wcel
    @37
    cfn
    wcel
    @89
    @35
    snfi
    @26
    @36
    unfi
    sylancl
    @123
    @64
    @123
    @124
    @125
    @132
    simprd
    recnd
    fsumsplit
    @59
    @140
    @72
    @65
    caddc
    @59
    @35
    cvv
    wcel
    @72
    cc
    wcel
    @140
    @72
    wceq
    @78
    @59
    @72
    @139
    recnd
    @64
    @72
    vm
    @35
    cvv
    @114
    @61
    @71
    cvol
    @79
    fveq2d
    sumsn
    sylancr
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    @31
    @63
    @32
    @65
    @30
    @62
    cvol
    @87
    fveq2i
    @26
    @2
    @64
    vk
    vm
    vm
    @2
    nfcv
    #
    @128
    @130
    cbvsumi
    eqeq12i
    @42
    @68
    @43
    @69
    @41
    @67
    cvol
    vk
    vm
    @37
    cB
    @61
    @84
    @85
    @86
    cbviun
    fveq2i
    @37
    @2
    @64
    vk
    vm
    @141
    @128
    @130
    cbvsumi
    eqeq12i
    3imtr4g
    ex
    a2d
    syl5
    findcard2s
    3impib
end
