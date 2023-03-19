include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfv.mm"
include "c4.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "clog.mm"
include "wceq.mm"
include "1nn.mm"
include "crp.mm"
include "stirlinglem2.mm"
include "relogcl.mm"
include "mp2b.mm"
include "cv.mm"
include "nfcv.mm"
include "cfa.mm"
include "c2.mm"
include "cmul.mm"
include "csqrt.mm"
include "ceu.mm"
include "cexp.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvmptf.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "a1i.mm"
include "relogcld.mm"
include "mpdan.mm"
include "eqeltrd.mm"
include "4re.mm"
include "4ne0.mm"
include "rereccli.mm"
include "cmin.mm"
include "cfz.mm"
include "caddc.mm"
include "csu.mm"
include "cle.mm"
include "cfzo.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "wa.mm"
include "cc.mm"
include "elfznn.mm"
include "syl.mm"
include "weq.mm"
include "syl2anc.mm"
include "adantl.mm"
include "rpcnd.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0d.mm"
include "logcld.mm"
include "telfsumo.mm"
include "cz.mm"
include "nnz.mm"
include "fzoval.mm"
include "sumeq1d.mm"
include "eqtr3d.mm"
include "fzfid.mm"
include "peano2nn.mm"
include "resubcld.mm"
include "fsumrecl.mm"
include "nnred.mm"
include "1red.mm"
include "readdcld.mm"
include "remulcld.mm"
include "recnd.mm"
include "1cnd.mm"
include "addcld.mm"
include "nnne0d.mm"
include "mulne0d.mm"
include "rereccld.mm"
include "wbr.mm"
include "eqid.mm"
include "stirlinglem10.mm"
include "fsumle.mm"
include "4pos.mm"
include "elrpii.mm"
include "0red.mm"
include "clt.mm"
include "0lt1.mm"
include "ltled.mm"
include "divge0d.mm"
include "eluznn.mm"
include "simpr.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "id.mm"
include "nnre.mm"
include "nncn.mm"
include "nnne0.mm"
include "fvmptd.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "seqeq1.mm"
include "trireciplem.mm"
include "climrel.mm"
include "releldmi.mm"
include "mp1i.mm"
include "wn.mm"
include "simpl.mm"
include "wo.mm"
include "elnn1uz2.mm"
include "sylib.mm"
include "ord.mm"
include "mpd.mm"
include "uz2m1nn.mm"
include "adantr.mm"
include "npcand.mm"
include "eqcomd.mm"
include "seqeq1d.mm"
include "nnuz.mm"
include "clim2ser.mm"
include "eqbrtrd.mm"
include "pm2.61dan.mm"
include "isumrecl.mm"
include "nnrpd.mm"
include "rpge0d.mm"
include "ge0p1rpd.mm"
include "rpmulcld.mm"
include "isumge0.mm"
include "leadd2dd.mm"
include "addid1d.mm"
include "mulcld.mm"
include "reccld.mm"
include "isumsplit.mm"
include "3brtr4d.mm"
include "wtru.mm"
include "1zzd.mm"
include "isumclim.mm"
include "trud.mm"
include "syl6breq.mm"
include "lemul2ad.mm"
include "4cn.mm"
include "gt0ne0d.mm"
include "fsummulc2.mm"
include "mulid1d.mm"
include "3brtr3d.mm"
include "letrd.mm"
include "subled.mm"

theorem stirlinglem12
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume stirlinglem12.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )
  assume stirlinglem12.2: |- B = ( n e. NN |-> ( log ` ( A ` n ) ) )
  assume stirlinglem12.3: |- F = ( n e. NN |-> ( 1 / ( n x. ( n + 1 ) ) ) )

  disjoint N n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint j k
  disjoint k n
  disjoint B j
  disjoint B k
  disjoint F j
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint k x
  assert |- ( N e. NN -> ( ( B ` 1 ) - ( 1 / 4 ) ) <_ ( B ` N ) )

  proof
    cN
    cn
    wcel
    #
    c1
    cB
    cfv
    #
    cN
    cB
    cfv
    #
    c1
    c4
    cdiv
    co
    #
    @1
    cr
    wcel
    @0
    @1
    c1
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    c1
    cn
    wcel
    #
    @5
    cr
    wcel
    #
    @1
    @5
    wceq
    1nn
    @6
    @4
    crp
    wcel
    @7
    1nn
    cA
    vn
    c1
    stirlinglem12.1
    stirlinglem2
    @4
    relogcl
    mp2b
    #
    vn
    c1
    vn
    cv
    #
    cA
    cfv
    #
    clog
    cfv
    #
    @5
    cn
    cB
    cr
    vn
    c1
    nfcv
    #
    vn
    @4
    clog
    vn
    clog
    nfcv
    #
    vn
    c1
    cA
    vn
    cA
    vn
    cn
    @9
    cfa
    cfv
    c2
    @9
    cmul
    co
    csqrt
    cfv
    @9
    ceu
    cdiv
    co
    @9
    cexp
    co
    cmul
    co
    cdiv
    co
    #
    cmpt
    stirlinglem12.1
    vn
    cn
    @14
    nfmpt1
    nfcxfr
    #
    @12
    nffv
    nffv
    @9
    c1
    wceq
    @10
    @4
    clog
    @9
    c1
    cA
    fveq2
    fveq2d
    stirlinglem12.2
    fvmptf
    mp2an
    @8
    eqeltri
    a1i
    @0
    @2
    cN
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @0
    @17
    cr
    wcel
    @2
    @17
    wceq
    @0
    @16
    cA
    vn
    cN
    stirlinglem12.1
    stirlinglem2
    relogcld
    #
    vn
    cN
    @11
    @17
    cn
    cB
    cr
    vn
    cN
    nfcv
    #
    vn
    @16
    clog
    @13
    vn
    cN
    cA
    @15
    @19
    nffv
    nffv
    @9
    cN
    wceq
    @10
    @16
    clog
    @9
    cN
    cA
    fveq2
    fveq2d
    stirlinglem12.2
    fvmptf
    mpdan
    @18
    eqeltrd
    @3
    cr
    wcel
    #
    @0
    c4
    4re
    4ne0
    rereccli
    #
    a1i
    #
    @0
    @1
    @2
    cmin
    co
    #
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vj
    cv
    #
    cB
    cfv
    #
    @26
    c1
    caddc
    co
    #
    cB
    cfv
    #
    cmin
    co
    #
    vj
    csu
    #
    @3
    cle
    @0
    c1
    cN
    cfzo
    co
    #
    @30
    vj
    csu
    @23
    @31
    @0
    vk
    cv
    #
    cB
    cfv
    #
    @27
    @29
    @1
    vj
    vk
    @2
    c1
    cN
    @33
    @26
    cB
    fveq2
    @33
    @28
    cB
    fveq2
    @33
    c1
    cB
    fveq2
    @33
    cN
    cB
    fveq2
    @0
    cN
    c1
    cuz
    cfv
    wcel
    cN
    elnnuz
    biimpi
    @0
    @33
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    @34
    @33
    cA
    cfv
    #
    clog
    cfv
    #
    cc
    @35
    @34
    @38
    wceq
    #
    @0
    @35
    @33
    cn
    wcel
    #
    @38
    cr
    wcel
    @39
    @33
    cN
    elfznn
    #
    @35
    @37
    @35
    @40
    @37
    crp
    wcel
    @41
    cA
    vn
    @33
    stirlinglem12.1
    stirlinglem2
    #
    syl
    #
    relogcld
    vn
    @33
    @11
    @38
    cn
    cB
    cr
    vn
    @33
    nfcv
    #
    vn
    @37
    clog
    @13
    vn
    @33
    cA
    @15
    @44
    nffv
    nffv
    vn
    vk
    weq
    @10
    @37
    clog
    @9
    @33
    cA
    fveq2
    fveq2d
    stirlinglem12.2
    fvmptf
    syl2anc
    adantl
    @36
    @37
    @35
    @37
    cc
    wcel
    @0
    @35
    @37
    @43
    rpcnd
    adantl
    @35
    @37
    cc0
    wne
    #
    @0
    @35
    @40
    @45
    @41
    @40
    @37
    @42
    rpne0d
    syl
    adantl
    logcld
    eqeltrd
    telfsumo
    @0
    @32
    @25
    @30
    vj
    @0
    cN
    cz
    wcel
    @32
    @25
    wceq
    cN
    nnz
    #
    c1
    cN
    fzoval
    syl
    sumeq1d
    eqtr3d
    @0
    @31
    @25
    @3
    c1
    @26
    @28
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    @3
    @0
    @25
    @30
    vj
    @0
    c1
    @24
    fzfid
    #
    @0
    @26
    @25
    wcel
    #
    wa
    #
    @27
    @29
    @53
    @26
    cn
    wcel
    #
    @27
    cr
    wcel
    @52
    @54
    @0
    @26
    @24
    elfznn
    #
    adantl
    #
    @54
    @27
    @26
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @54
    @58
    cr
    wcel
    @27
    @58
    wceq
    @54
    @57
    cA
    vn
    @26
    stirlinglem12.1
    stirlinglem2
    relogcld
    #
    vn
    @26
    @11
    @58
    cn
    cB
    cr
    vn
    @26
    nfcv
    #
    vn
    @57
    clog
    @13
    vn
    @26
    cA
    @15
    @60
    nffv
    nffv
    vn
    vj
    weq
    #
    @10
    @57
    clog
    @9
    @26
    cA
    fveq2
    fveq2d
    stirlinglem12.2
    fvmptf
    mpdan
    @59
    eqeltrd
    syl
    @52
    @29
    cr
    wcel
    #
    @0
    @52
    @54
    @62
    @55
    @54
    @29
    @28
    cA
    cfv
    #
    clog
    cfv
    #
    cr
    @54
    @28
    cn
    wcel
    #
    @64
    cr
    wcel
    @29
    @64
    wceq
    @26
    peano2nn
    #
    @54
    @63
    @54
    @65
    @63
    crp
    wcel
    @66
    cA
    vn
    @28
    stirlinglem12.1
    stirlinglem2
    syl
    relogcld
    #
    vn
    @28
    @11
    @64
    cn
    cB
    cr
    vn
    @28
    nfcv
    #
    vn
    @63
    clog
    @13
    vn
    @28
    cA
    @15
    @68
    nffv
    nffv
    @9
    @28
    wceq
    @10
    @63
    clog
    @9
    @28
    cA
    fveq2
    fveq2d
    stirlinglem12.2
    fvmptf
    syl2anc
    @67
    eqeltrd
    syl
    adantl
    resubcld
    #
    fsumrecl
    @0
    @25
    @49
    vj
    @51
    @53
    @3
    @48
    @20
    @53
    @21
    a1i
    @52
    @48
    cr
    wcel
    @0
    @52
    @47
    @52
    @26
    @28
    @52
    @26
    @55
    nnred
    #
    @52
    @26
    c1
    @70
    @52
    1red
    readdcld
    remulcld
    @52
    @26
    @28
    @52
    @26
    @70
    recnd
    #
    @52
    @26
    c1
    @71
    @52
    1cnd
    addcld
    @52
    @26
    @55
    nnne0d
    @52
    @54
    @28
    cc0
    wne
    #
    @55
    @54
    @28
    @66
    nnne0d
    #
    syl
    mulne0d
    rereccld
    adantl
    #
    remulcld
    #
    fsumrecl
    @22
    @0
    @25
    @30
    @49
    vj
    @51
    @69
    @75
    @53
    @54
    @30
    @49
    cle
    wbr
    @56
    cA
    cB
    vi
    vn
    vi
    cn
    c1
    c2
    vi
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    cdiv
    co
    c1
    c2
    @26
    cmul
    co
    c1
    caddc
    co
    #
    cdiv
    co
    @77
    cexp
    co
    cmul
    co
    cmpt
    #
    vi
    cn
    c1
    @78
    c2
    cexp
    co
    cdiv
    co
    @76
    cexp
    co
    cmpt
    #
    @26
    stirlinglem12.1
    stirlinglem12.2
    @79
    eqid
    @80
    eqid
    stirlinglem10
    syl
    fsumle
    @0
    @3
    @25
    @48
    vj
    csu
    #
    cmul
    co
    @3
    c1
    cmul
    co
    @50
    @3
    cle
    @0
    @81
    c1
    @3
    @0
    @25
    @48
    vj
    @51
    @74
    fsumrecl
    #
    @0
    1red
    #
    @22
    @0
    c1
    c4
    @83
    c4
    crp
    wcel
    @0
    c4
    4re
    4pos
    elrpii
    a1i
    @0
    cc0
    c1
    @0
    0red
    #
    @83
    cc0
    c1
    clt
    wbr
    @0
    0lt1
    a1i
    ltled
    #
    divge0d
    @0
    @81
    cn
    @48
    vj
    csu
    #
    c1
    cle
    @0
    @81
    cc0
    caddc
    co
    #
    @81
    cN
    cuz
    cfv
    #
    @48
    vj
    csu
    #
    caddc
    co
    @81
    @86
    cle
    @0
    cc0
    @89
    @81
    @84
    @0
    @48
    vj
    cF
    cN
    @88
    @88
    eqid
    #
    @46
    @0
    @26
    @88
    wcel
    #
    wa
    #
    @54
    @26
    cF
    cfv
    #
    @48
    wceq
    #
    @26
    cN
    eluznn
    #
    @54
    vn
    @26
    c1
    @9
    @9
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    @48
    cn
    cF
    cr
    cF
    vn
    cn
    @98
    cmpt
    wceq
    @54
    stirlinglem12.3
    a1i
    @54
    @61
    wa
    #
    @97
    @47
    c1
    cdiv
    @99
    @9
    @26
    @96
    @28
    cmul
    @54
    @61
    simpr
    #
    @99
    @9
    @26
    c1
    caddc
    @100
    oveq1d
    oveq12d
    oveq2d
    @54
    id
    @54
    @47
    @54
    @26
    @28
    @26
    nnre
    #
    @54
    @26
    c1
    @101
    @54
    1red
    readdcld
    remulcld
    @54
    @26
    @28
    @26
    nncn
    #
    @54
    @26
    c1
    @102
    @54
    1cnd
    addcld
    @26
    nnne0
    #
    @73
    mulne0d
    rereccld
    #
    fvmptd
    #
    syl
    #
    @92
    @47
    @92
    @26
    @28
    @92
    @26
    @95
    nnred
    #
    @92
    @26
    c1
    @107
    @92
    1red
    #
    readdcld
    remulcld
    @92
    @26
    @28
    @92
    @26
    @107
    recnd
    #
    @92
    @26
    c1
    @109
    @92
    1cnd
    addcld
    @92
    @26
    @95
    nnne0d
    @92
    @54
    @72
    @95
    @73
    syl
    mulne0d
    rereccld
    #
    @0
    cN
    c1
    wceq
    #
    caddc
    cF
    cN
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    @111
    @114
    @0
    @111
    @112
    caddc
    cF
    c1
    cseq
    #
    @113
    caddc
    cF
    cN
    c1
    seqeq1
    @115
    c1
    cli
    wbr
    #
    @115
    @113
    wcel
    #
    @111
    vn
    cF
    stirlinglem12.3
    trireciplem
    #
    @115
    c1
    cli
    climrel
    releldmi
    #
    mp1i
    eqeltrd
    adantl
    @0
    @111
    wn
    #
    wa
    #
    @0
    @24
    cn
    wcel
    #
    @114
    @0
    @120
    simpl
    #
    @121
    cN
    c2
    cuz
    cfv
    wcel
    #
    @122
    @121
    @120
    @124
    @0
    @120
    simpr
    @121
    @111
    @124
    @121
    @0
    @111
    @124
    wo
    @123
    cN
    elnn1uz2
    sylib
    ord
    mpd
    cN
    uz2m1nn
    syl
    @0
    @122
    wa
    #
    @112
    c1
    @24
    @115
    cfv
    cmin
    co
    #
    cli
    wbr
    @114
    @125
    @112
    caddc
    cF
    @24
    c1
    caddc
    co
    #
    cseq
    #
    @126
    cli
    @125
    cN
    @127
    caddc
    cF
    @125
    @127
    cN
    @125
    cN
    c1
    @0
    cN
    cc
    wcel
    @122
    cN
    nncn
    adantr
    @125
    1cnd
    npcand
    eqcomd
    seqeq1d
    @122
    @128
    @126
    cli
    wbr
    @0
    @122
    c1
    vj
    cF
    c1
    @24
    cn
    nnuz
    @122
    id
    @54
    @93
    cc
    wcel
    @122
    @54
    @93
    @48
    cc
    @105
    @54
    @48
    @104
    recnd
    #
    eqeltrd
    adantl
    @116
    @122
    @118
    a1i
    clim2ser
    adantl
    eqbrtrd
    @112
    @126
    cli
    climrel
    releldmi
    syl
    syl2anc
    pm2.61dan
    #
    isumrecl
    @82
    @0
    @48
    vj
    cF
    cN
    @88
    @90
    @46
    @106
    @110
    @130
    @92
    c1
    @47
    @108
    @92
    @26
    @28
    @92
    @26
    @95
    nnrpd
    #
    @92
    @26
    @107
    @92
    @26
    @131
    rpge0d
    ge0p1rpd
    rpmulcld
    @0
    cc0
    c1
    cle
    wbr
    @91
    @85
    adantr
    divge0d
    isumge0
    leadd2dd
    @0
    @87
    @81
    @0
    @81
    @0
    @81
    @82
    recnd
    addid1d
    eqcomd
    @0
    @48
    vj
    cF
    c1
    cN
    @88
    cn
    nnuz
    @90
    @0
    id
    @54
    @94
    @0
    @105
    adantl
    @0
    @54
    wa
    #
    @47
    @132
    @26
    @28
    @54
    @26
    cc
    wcel
    @0
    @102
    adantl
    #
    @132
    @26
    c1
    @133
    @132
    1cnd
    addcld
    #
    mulcld
    @132
    @26
    @28
    @133
    @134
    @54
    @26
    cc0
    wne
    @0
    @103
    adantl
    @54
    @72
    @0
    @73
    adantl
    mulne0d
    reccld
    @116
    @117
    @0
    @118
    @119
    mp1i
    isumsplit
    3brtr4d
    @86
    c1
    wceq
    wtru
    @48
    c1
    vj
    cF
    c1
    cn
    nnuz
    wtru
    1zzd
    @54
    @94
    wtru
    @105
    adantl
    @54
    @48
    cc
    wcel
    wtru
    @129
    adantl
    @116
    wtru
    @118
    a1i
    isumclim
    trud
    syl6breq
    lemul2ad
    @0
    @25
    @48
    @3
    vj
    @51
    @0
    c4
    c4
    cc
    wcel
    @0
    4cn
    a1i
    @0
    c4
    cc0
    c4
    clt
    wbr
    @0
    4pos
    a1i
    gt0ne0d
    reccld
    #
    @53
    @48
    @74
    recnd
    fsummulc2
    @0
    @3
    @135
    mulid1d
    3brtr3d
    letrd
    eqbrtrd
    subled
end
