include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cneg.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "cc0.mm"
include "cmin.mm"
include "cfz.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cn0.mm"
include "simpl2.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "neg1cn.mm"
include "cr.mm"
include "2re.mm"
include "simp2.mm"
include "nndivre.mm"
include "sylancr.mm"
include "recnd.mm"
include "cxpcl.mm"
include "adantr.mm"
include "0nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "mul02d.mm"
include "simprl.mm"
include "oveq1d.mm"
include "simprr.mm"
include "0expd.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "nncn.mm"
include "nnne0.mm"
include "reccl.mm"
include "recne0.mm"
include "0cxpd.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "expr.mm"
include "clog.mm"
include "ci.mm"
include "cpi.mm"
include "caddc.mm"
include "cz.mm"
include "ce.mm"
include "simpl1.mm"
include "simpr.mm"
include "nnzd.mm"
include "explog.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "wb.mm"
include "nncnd.mm"
include "logcld.mm"
include "mulcld.mm"
include "nnnn0d.mm"
include "expcld.mm"
include "expne0d.mm"
include "eflogeq.mm"
include "mpbid.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "zcn.mm"
include "adantl.mm"
include "mulcl.mm"
include "addcld.mm"
include "nnne0d.mm"
include "ad2antrr.mm"
include "divmuld.mm"
include "fveq2.mm"
include "cmo.mm"
include "reccld.mm"
include "efadd.mm"
include "divdird.mm"
include "divrec2d.mm"
include "a1i.mm"
include "div23d.mm"
include "mul12i.mm"
include "oveq1i.mm"
include "syl5eq.mm"
include "mul32d.mm"
include "3eqtrd.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "cxpefd.mm"
include "neg1ne0.mm"
include "cxpmul2zd.mm"
include "logm1.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "cxpcld.mm"
include "cxpne0d.mm"
include "expclzd.mm"
include "zmodcld.mm"
include "nn0zd.mm"
include "expsubd.mm"
include "crp.mm"
include "zre.mm"
include "nnrpd.mm"
include "moddifz.mm"
include "expmulz.mm"
include "syl22anc.mm"
include "nn0cnd.mm"
include "subcld.mm"
include "divcan2d.mm"
include "root1id.mm"
include "1exp.mm"
include "eqtr3d.mm"
include "diveq1d.mm"
include "3eqtr3rd.mm"
include "3eqtr4d.mm"
include "eflog.mm"
include "eqeq12d.mm"
include "zmodfz.mm"
include "eqcom.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "ex.mm"
include "sylbid.mm"
include "syl5.mm"
include "sylbird.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "oveq1.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "pm2.61dane.mm"
include "simp3.mm"
include "nnrecre.mm"
include "3ad2ant2.mm"
include "elfznn0.mm"
include "syl2an.mm"
include "mulexpd.mm"
include "cxproot.mm"
include "mulcomd.mm"
include "expmuld.mm"
include "elfzelz.mm"
include "mulid1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem cxpeq
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cN: class N
  let vm: setvar m

  disjoint A n
  disjoint B n
  disjoint N n
  disjoint m n
  disjoint A m
  disjoint B m
  disjoint N m
  assert |- ( ( A e. CC /\ N e. NN /\ B e. CC ) -> ( ( A ^ N ) = B <-> E. n e. ( 0 ... ( N - 1 ) ) A = ( ( B ^c ( 1 / N ) ) x. ( ( -u 1 ^c ( 2 / N ) ) ^ n ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    cB
    cc
    wcel
    #
    w3a
    #
    cA
    cN
    cexp
    co
    #
    cB
    wceq
    #
    cA
    cB
    c1
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    c1
    cneg
    #
    c2
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    vn
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    vn
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @3
    @5
    @17
    wi
    cA
    cc0
    @3
    cA
    cc0
    wceq
    #
    @5
    @17
    @3
    @18
    @5
    wa
    #
    wa
    #
    cc0
    @16
    wcel
    #
    cA
    @7
    @10
    cc0
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    @17
    @20
    @15
    cc0
    cuz
    cfv
    #
    wcel
    @21
    @20
    @15
    cn0
    @25
    @20
    @1
    @15
    cn0
    wcel
    @0
    @1
    @2
    @19
    simpl2
    #
    cN
    nnm1nn0
    syl
    nn0uz
    syl6eleq
    cc0
    @15
    eluzfz1
    syl
    @20
    cc0
    @22
    cmul
    co
    cc0
    @23
    cA
    @20
    @22
    @20
    @10
    cc
    wcel
    #
    cc0
    cn0
    wcel
    @22
    cc
    wcel
    @3
    @27
    @19
    @3
    @8
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @27
    neg1cn
    @3
    @9
    @3
    c2
    cr
    wcel
    @1
    @9
    cr
    wcel
    2re
    @0
    @1
    @2
    simp2
    #
    c2
    cN
    nndivre
    sylancr
    recnd
    #
    @8
    @9
    cxpcl
    sylancr
    #
    adantr
    0nn0
    @10
    cc0
    expcl
    sylancl
    mul02d
    @20
    @7
    cc0
    @22
    cmul
    @20
    @7
    cc0
    @6
    ccxp
    co
    #
    cc0
    @20
    cB
    cc0
    @6
    ccxp
    @20
    @4
    cc0
    cN
    cexp
    co
    cB
    cc0
    @20
    cA
    cc0
    cN
    cexp
    @3
    @18
    @5
    simprl
    #
    oveq1d
    @3
    @18
    @5
    simprr
    @20
    cN
    @26
    0expd
    3eqtr3d
    oveq1d
    @20
    @1
    @33
    cc0
    wceq
    #
    @26
    @1
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    @35
    cN
    nncn
    cN
    nnne0
    @36
    @37
    wa
    @6
    cN
    reccl
    cN
    recne0
    0cxpd
    syl2anc
    syl
    eqtrd
    oveq1d
    @34
    3eqtr4rd
    @14
    @24
    vn
    cc0
    @16
    @11
    cc0
    wceq
    #
    @13
    @23
    cA
    @38
    @12
    @22
    @7
    cmul
    @11
    cc0
    @10
    cexp
    oveq2
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    expr
    @3
    cA
    cc0
    wne
    #
    wa
    #
    cA
    @4
    @6
    ccxp
    co
    #
    @12
    cmul
    co
    #
    wceq
    #
    vn
    @16
    wrex
    #
    @5
    @17
    @40
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    #
    @4
    clog
    cfv
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    vm
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vm
    cz
    wrex
    #
    @44
    @40
    @46
    ce
    cfv
    #
    @4
    wceq
    #
    @54
    @40
    @4
    @55
    @40
    @0
    @39
    cN
    cz
    wcel
    #
    @4
    @55
    wceq
    @0
    @1
    @2
    @39
    simpl1
    #
    @3
    @39
    simpr
    #
    @40
    cN
    @0
    @1
    @2
    @39
    simpl2
    #
    nnzd
    #
    cA
    cN
    explog
    syl3anc
    eqcomd
    @40
    @46
    cc
    wcel
    @4
    cc
    wcel
    #
    @4
    cc0
    wne
    #
    @56
    @54
    wb
    @40
    cN
    @45
    @3
    @36
    @39
    @3
    cN
    @30
    nncnd
    adantr
    #
    @40
    cA
    @58
    @59
    logcld
    #
    mulcld
    @40
    cA
    cN
    @58
    @40
    cN
    @60
    nnnn0d
    expcld
    #
    @40
    cA
    cN
    @58
    @59
    @61
    expne0d
    #
    @46
    @4
    vm
    eflogeq
    syl3anc
    mpbid
    @40
    @53
    @44
    vm
    cz
    @40
    @50
    cz
    wcel
    #
    wa
    #
    @53
    @52
    cN
    cdiv
    co
    #
    @45
    wceq
    #
    @44
    @69
    @52
    cN
    @45
    @69
    @47
    @51
    @40
    @47
    cc
    wcel
    @68
    @40
    @4
    @66
    @67
    logcld
    adantr
    #
    @69
    @49
    cc
    wcel
    #
    @50
    cc
    wcel
    #
    @51
    cc
    wcel
    ci
    @48
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    #
    @68
    @74
    @40
    @50
    zcn
    adantl
    #
    @49
    @50
    mulcl
    sylancr
    #
    addcld
    @40
    @36
    @68
    @64
    adantr
    #
    @40
    @45
    cc
    wcel
    @68
    @65
    adantr
    @3
    @37
    @39
    @68
    @3
    cN
    @30
    nnne0d
    ad2antrr
    #
    divmuld
    @71
    @70
    ce
    cfv
    #
    @45
    ce
    cfv
    #
    wceq
    #
    @69
    @44
    @70
    @45
    ce
    fveq2
    @69
    @82
    @41
    @10
    @50
    cN
    cmo
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cA
    wceq
    #
    @44
    @69
    @80
    @85
    @81
    cA
    @69
    @6
    @47
    cmul
    co
    #
    @9
    @50
    cmul
    co
    #
    ci
    cpi
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    ce
    cfv
    #
    @87
    ce
    cfv
    #
    @90
    ce
    cfv
    #
    cmul
    co
    #
    @80
    @85
    @69
    @87
    cc
    wcel
    @90
    cc
    wcel
    #
    @92
    @95
    wceq
    @69
    @6
    @47
    @69
    cN
    @78
    @79
    reccld
    #
    @72
    mulcld
    @69
    @88
    cc
    wcel
    @89
    cc
    wcel
    #
    @96
    @69
    @9
    @50
    @3
    @29
    @39
    @68
    @31
    ad2antrr
    #
    @76
    mulcld
    #
    ci
    cpi
    ax-icn
    picn
    mulcli
    #
    @88
    @89
    mulcl
    sylancl
    @87
    @90
    efadd
    syl2anc
    @69
    @70
    @91
    ce
    @69
    @70
    @47
    cN
    cdiv
    co
    #
    @51
    cN
    cdiv
    co
    #
    caddc
    co
    @91
    @69
    @47
    @51
    cN
    @72
    @77
    @78
    @79
    divdird
    @69
    @102
    @87
    @103
    @90
    caddc
    @69
    @47
    cN
    @72
    @78
    @79
    divrec2d
    @69
    @103
    @49
    cN
    cdiv
    co
    #
    @50
    cmul
    co
    @9
    @89
    cmul
    co
    #
    @50
    cmul
    co
    @90
    @69
    @49
    @50
    cN
    @73
    @69
    @75
    a1i
    @76
    @78
    @79
    div23d
    @69
    @104
    @105
    @50
    cmul
    @69
    @104
    c2
    @89
    cmul
    co
    #
    cN
    cdiv
    co
    @105
    @49
    @106
    cN
    cdiv
    ci
    c2
    cpi
    ax-icn
    2cn
    picn
    mul12i
    oveq1i
    @69
    c2
    @89
    cN
    c2
    cc
    wcel
    @69
    2cn
    a1i
    @98
    @69
    @101
    a1i
    #
    @78
    @79
    div23d
    syl5eq
    oveq1d
    @69
    @9
    @89
    @50
    @99
    @107
    @76
    mul32d
    3eqtrd
    oveq12d
    eqtrd
    fveq2d
    @69
    @41
    @93
    @84
    @94
    cmul
    @69
    @4
    @6
    @40
    @62
    @68
    @66
    adantr
    @40
    @63
    @68
    @67
    adantr
    @97
    cxpefd
    @69
    @8
    @88
    ccxp
    co
    #
    @10
    @50
    cexp
    co
    #
    @94
    @84
    @69
    @8
    @9
    @50
    @28
    @69
    neg1cn
    a1i
    #
    @8
    cc0
    wne
    #
    @69
    neg1ne0
    a1i
    #
    @99
    @40
    @68
    simpr
    #
    cxpmul2zd
    @69
    @108
    @88
    @8
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    @94
    @69
    @8
    @88
    @110
    @112
    @100
    cxpefd
    @115
    @90
    ce
    @114
    @89
    @88
    cmul
    logm1
    oveq2i
    fveq2i
    syl6eq
    @69
    @109
    @84
    @69
    @10
    @50
    @69
    @8
    @9
    @110
    @99
    cxpcld
    #
    @3
    @10
    cc0
    wne
    #
    @39
    @68
    @3
    @8
    @9
    @28
    @3
    neg1cn
    a1i
    @111
    @3
    neg1ne0
    a1i
    @31
    cxpne0d
    ad2antrr
    #
    @113
    expclzd
    @69
    @10
    @83
    @116
    @69
    @50
    cN
    @113
    @40
    @1
    @68
    @60
    adantr
    #
    zmodcld
    #
    expcld
    @69
    @10
    @83
    @116
    @118
    @69
    @83
    @120
    nn0zd
    #
    expne0d
    @69
    @10
    @50
    @83
    cmin
    co
    #
    cexp
    co
    #
    @109
    @84
    cdiv
    co
    c1
    @69
    @10
    @50
    @83
    @116
    @118
    @121
    @113
    expsubd
    @69
    @10
    cN
    @122
    cN
    cdiv
    co
    #
    cmul
    co
    #
    cexp
    co
    #
    @10
    cN
    cexp
    co
    #
    @124
    cexp
    co
    #
    @123
    c1
    @69
    @27
    @117
    @57
    @124
    cz
    wcel
    #
    @126
    @128
    wceq
    @116
    @118
    @69
    cN
    @119
    nnzd
    @69
    @50
    cr
    wcel
    #
    cN
    crp
    wcel
    @129
    @68
    @130
    @40
    @50
    zre
    adantl
    @69
    cN
    @119
    nnrpd
    @50
    cN
    moddifz
    syl2anc
    #
    @10
    cN
    @124
    expmulz
    syl22anc
    @69
    @125
    @122
    @10
    cexp
    @69
    @122
    cN
    @69
    @50
    @83
    @76
    @69
    @83
    @120
    nn0cnd
    subcld
    @78
    @79
    divcan2d
    oveq2d
    @69
    @128
    c1
    @124
    cexp
    co
    #
    c1
    @69
    @127
    c1
    @124
    cexp
    @69
    @1
    @127
    c1
    wceq
    #
    @119
    cN
    root1id
    #
    syl
    oveq1d
    @69
    @129
    @132
    c1
    wceq
    @131
    @124
    1exp
    syl
    eqtrd
    3eqtr3d
    eqtr3d
    diveq1d
    3eqtr3rd
    oveq12d
    3eqtr4d
    @40
    @81
    cA
    wceq
    #
    @68
    @40
    @0
    @39
    @135
    @58
    @59
    cA
    eflog
    syl2anc
    adantr
    eqeq12d
    @69
    @83
    @16
    wcel
    #
    @86
    @44
    wi
    @69
    @68
    @1
    @136
    @113
    @119
    @50
    cN
    zmodfz
    syl2anc
    @136
    @86
    @44
    @43
    @86
    vn
    @83
    @16
    @43
    @42
    cA
    wceq
    @11
    @83
    wceq
    #
    @86
    cA
    @42
    eqcom
    @137
    @42
    @85
    cA
    @137
    @12
    @84
    @41
    cmul
    @11
    @83
    @10
    cexp
    oveq2
    oveq2d
    eqeq1d
    syl5bb
    rspcev
    ex
    syl
    sylbid
    syl5
    sylbird
    rexlimdva
    mpd
    @5
    @43
    @14
    vn
    @16
    @5
    @42
    @13
    cA
    @5
    @41
    @7
    @12
    cmul
    @4
    cB
    @6
    ccxp
    oveq1
    oveq1d
    eqeq2d
    rexbidv
    syl5ibcom
    pm2.61dane
    @3
    @14
    @5
    vn
    @16
    @3
    @11
    @16
    wcel
    #
    wa
    #
    @5
    @14
    @13
    cN
    cexp
    co
    #
    cB
    wceq
    @139
    @140
    @7
    cN
    cexp
    co
    #
    @12
    cN
    cexp
    co
    #
    cmul
    co
    cB
    c1
    cmul
    co
    cB
    @139
    @7
    @12
    cN
    @3
    @7
    cc
    wcel
    @138
    @3
    cB
    @6
    @0
    @1
    @2
    simp3
    #
    @3
    @6
    @1
    @0
    @6
    cr
    wcel
    @2
    cN
    nnrecre
    3ad2ant2
    recnd
    cxpcld
    adantr
    @3
    @27
    @11
    cn0
    wcel
    #
    @12
    cc
    wcel
    @138
    @32
    @11
    @15
    elfznn0
    #
    @10
    @11
    expcl
    syl2an
    @139
    cN
    @3
    @1
    @138
    @30
    adantr
    #
    nnnn0d
    #
    mulexpd
    @139
    @141
    cB
    @142
    c1
    cmul
    @139
    @2
    @1
    @141
    cB
    wceq
    @3
    @2
    @138
    @143
    adantr
    #
    @146
    cB
    cN
    cxproot
    syl2anc
    @139
    @142
    @127
    @11
    cexp
    co
    #
    c1
    @11
    cexp
    co
    #
    c1
    @139
    @10
    @11
    cN
    cmul
    co
    #
    cexp
    co
    @10
    cN
    @11
    cmul
    co
    #
    cexp
    co
    @142
    @149
    @139
    @151
    @152
    @10
    cexp
    @139
    @11
    cN
    @139
    @11
    @138
    @144
    @3
    @145
    adantl
    #
    nn0cnd
    @139
    cN
    @146
    nncnd
    mulcomd
    oveq2d
    @139
    @10
    @11
    cN
    @3
    @27
    @138
    @32
    adantr
    #
    @147
    @153
    expmuld
    @139
    @10
    cN
    @11
    @154
    @153
    @147
    expmuld
    3eqtr3d
    @139
    @127
    c1
    @11
    cexp
    @139
    @1
    @133
    @146
    @134
    syl
    oveq1d
    @139
    @11
    cz
    wcel
    #
    @150
    c1
    wceq
    @138
    @155
    @3
    @11
    cc0
    @15
    elfzelz
    adantl
    @11
    1exp
    syl
    3eqtrd
    oveq12d
    @139
    cB
    @148
    mulid1d
    3eqtrd
    @14
    @4
    @140
    cB
    cA
    @13
    cN
    cexp
    oveq1
    eqeq1d
    syl5ibrcom
    rexlimdva
    impbid
end
