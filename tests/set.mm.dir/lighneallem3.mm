include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wi.mm"
include "oveq2.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "2m1e1.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "cz.mm"
include "cn0.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nnnn0.mm"
include "3syl.mm"
include "nn0zd.mm"
include "iddvdsexp.mm"
include "sylan.mm"
include "wb.mm"
include "breq2.mm"
include "dvds1.mm"
include "syl.mm"
include "eleq1.mm"
include "1nprm.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "sylbid.mm"
include "ad2antrr.mm"
include "sylbird.mm"
include "ex.mm"
include "mpid.mm"
include "adantr.mm"
include "com23.mm"
include "a1d.mm"
include "3adant3.mm"
include "3imp.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "wne.mm"
include "neqne.mm"
include "anim2i.mm"
include "eluz2b3.mm"
include "sylibr.mm"
include "oddge22np1.mm"
include "3ad2antl3.mm"
include "eqcoms.mm"
include "a1i.mm"
include "2nn0.mm"
include "nn0mulcld.mm"
include "expp1d.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "peano2cnm.mm"
include "1cnd.mm"
include "adddid.mm"
include "mulcld.mm"
include "ax-1cn.mm"
include "mulcli.mm"
include "addsubassd.mm"
include "2t1e2.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "3eqtrd.mm"
include "ad2antlr.mm"
include "sylan9eqr.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "subadd2.mm"
include "cc0.mm"
include "cfz.mm"
include "csu.mm"
include "nncn.mm"
include "pwm1geoser.mm"
include "cdiv.mm"
include "subcld.mm"
include "fzfid.mm"
include "elfznn0.mm"
include "fsumzcl.mm"
include "zcnd.mm"
include "crp.mm"
include "2rp.mm"
include "rpcnne0d.mm"
include "divmul2.mm"
include "syl3anc.mm"
include "div23.mm"
include "2nn.mm"
include "id.mm"
include "nnmulcld.mm"
include "syl2anc.mm"
include "notnotd.mm"
include "oddm1even.mm"
include "mtbid.mm"
include "notbid.mm"
include "wo.mm"
include "ad4ant14.mm"
include "elnn0.mm"
include "eldifsn.mm"
include "simpr.mm"
include "necomd.mm"
include "sylbi.mm"
include "neneqd.mm"
include "2prm.mm"
include "simpl.mm"
include "prmdvdsexpb.mm"
include "mp3an2i.mm"
include "mtbird.mm"
include "n2dvds1.mm"
include "exp0d.mm"
include "sylan9eq.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "jaoi.mm"
include "syl11.mm"
include "imp.mm"
include "chash.mm"
include "nnm1nn0.mm"
include "hashfz0.mm"
include "npcand.mm"
include "eqtr2d.mm"
include "biimpa.mm"
include "evensumodd.mm"
include "olcd.mm"
include "oddn2prm.mm"
include "oddm1d2.mm"
include "mpbid.mm"
include "euclemma.mm"
include "mpbird.mm"
include "pm2.24d.mm"
include "exp31.mm"
include "rexlimdva.mm"
include "com34.mm"
include "com24.mm"
include "com25.mm"
include "impd.mm"
include "pm2.61d.mm"

theorem lighneallem3
  let cP: class P
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vj: setvar j
  let vx: setvar x


  assert |- ( ( ( P e. ( Prime \ { 2 } ) /\ M e. NN /\ N e. NN ) /\ ( -. 2 || N /\ 2 || M ) /\ ( ( 2 ^ N ) - 1 ) = ( P ^ M ) ) -> M = 1 )

  proof
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    c2
    cM
    cdvds
    wbr
    #
    wa
    #
    c2
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    cP
    cM
    cexp
    co
    #
    wceq
    #
    w3a
    cN
    c1
    wceq
    #
    cM
    c1
    wceq
    #
    @4
    @7
    @11
    @12
    @13
    wi
    #
    @1
    @2
    @7
    @11
    @14
    wi
    #
    wi
    @3
    @1
    @2
    wa
    #
    @15
    @7
    @16
    @12
    @11
    @13
    @16
    @12
    @11
    @13
    wi
    #
    @16
    @12
    wa
    #
    @11
    c1
    @10
    wceq
    #
    @13
    @18
    @9
    c1
    @10
    @12
    @9
    c1
    wceq
    @16
    @12
    @9
    c2
    c1
    cmin
    co
    #
    c1
    @12
    @8
    c2
    c1
    cmin
    @12
    @8
    c2
    c1
    cexp
    co
    #
    c2
    cN
    c1
    c2
    cexp
    oveq2
    c2
    cc
    wcel
    #
    @21
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    syl6eq
    oveq1d
    2m1e1
    syl6eq
    adantl
    eqeq1d
    @16
    @19
    @13
    wi
    @12
    @16
    @19
    cP
    @10
    cdvds
    wbr
    #
    @13
    @1
    cP
    cz
    wcel
    #
    @2
    @23
    @1
    cP
    @1
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    #
    cP
    cn0
    wcel
    #
    cP
    cprime
    @0
    eldifi
    #
    cP
    prmnn
    #
    cP
    nnnn0
    3syl
    #
    nn0zd
    #
    cP
    cM
    iddvdsexp
    sylan
    @16
    @19
    @23
    @13
    wi
    @16
    @19
    wa
    @23
    cP
    c1
    cdvds
    wbr
    #
    @13
    @19
    @32
    @23
    wb
    @16
    c1
    @10
    cP
    cdvds
    breq2
    adantl
    @1
    @32
    @13
    wi
    @2
    @19
    @1
    @32
    cP
    c1
    wceq
    #
    @13
    @1
    @27
    @32
    @33
    wb
    @30
    cP
    dvds1
    syl
    @1
    @25
    @33
    @13
    @28
    @33
    @25
    c1
    cprime
    wcel
    #
    @13
    cP
    c1
    cprime
    eleq1
    @34
    @13
    1nprm
    pm2.21i
    syl6bi
    syl5com
    sylbid
    ad2antrr
    sylbird
    ex
    mpid
    adantr
    sylbid
    ex
    com23
    a1d
    3adant3
    3imp
    @4
    @7
    @11
    @12
    wn
    #
    @13
    wi
    #
    @4
    @5
    @6
    @11
    @36
    wi
    @4
    @35
    @6
    @11
    @5
    @13
    @4
    @35
    @6
    @11
    @5
    @13
    wi
    wi
    wi
    @4
    @35
    wa
    #
    @5
    @11
    @6
    @13
    @37
    @5
    c2
    vj
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    vj
    cn
    wrex
    #
    @11
    @6
    @13
    wi
    wi
    #
    @3
    @1
    @35
    @5
    @42
    wb
    #
    @2
    @3
    @35
    wa
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    @44
    @45
    @3
    cN
    c1
    wne
    #
    wa
    @46
    @35
    @47
    @3
    cN
    c1
    neqne
    anim2i
    cN
    eluz2b3
    sylibr
    vj
    cN
    oddge22np1
    syl
    3ad2antl3
    @4
    @42
    @43
    wi
    @35
    @4
    @42
    @6
    @11
    @13
    @4
    @41
    @6
    @17
    wi
    vj
    cn
    @4
    @38
    cn
    wcel
    #
    wa
    #
    @6
    @41
    @17
    @49
    @6
    @41
    @17
    @49
    @6
    wa
    #
    @41
    wa
    #
    @11
    c2
    c2
    @39
    cexp
    co
    #
    c1
    cmin
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @10
    wceq
    #
    @13
    @51
    @9
    @55
    @10
    @41
    @50
    @9
    c2
    @40
    cexp
    co
    #
    c1
    cmin
    co
    #
    @55
    @9
    @58
    wceq
    cN
    @40
    cN
    @40
    wceq
    @8
    @57
    c1
    cmin
    cN
    @40
    c2
    cexp
    oveq2
    oveq1d
    eqcoms
    @48
    @58
    @55
    wceq
    @4
    @6
    @48
    @58
    c2
    @52
    cmul
    co
    #
    c1
    cmin
    co
    @54
    c2
    c1
    cmul
    co
    #
    caddc
    co
    #
    c1
    cmin
    co
    #
    @55
    @48
    @57
    @59
    c1
    cmin
    @48
    @57
    @52
    c2
    cmul
    co
    @59
    @48
    c2
    @39
    @22
    @48
    2cn
    a1i
    #
    @48
    c2
    @38
    c2
    cn0
    wcel
    @48
    2nn0
    a1i
    #
    @38
    nnnn0
    nn0mulcld
    #
    expp1d
    @48
    @52
    c2
    @48
    @52
    @48
    c2
    @39
    @64
    @65
    nn0expcld
    #
    nn0cnd
    #
    @63
    mulcomd
    eqtrd
    oveq1d
    @48
    @59
    @61
    c1
    cmin
    @48
    @59
    c2
    @53
    c1
    caddc
    co
    #
    cmul
    co
    @61
    @48
    @52
    @68
    c2
    cmul
    @48
    @68
    @52
    @48
    @52
    cc
    wcel
    #
    @68
    @52
    wceq
    @67
    @52
    npcan1
    syl
    eqcomd
    oveq2d
    @48
    c2
    @53
    c1
    @63
    @48
    @69
    @53
    cc
    wcel
    #
    @67
    @52
    peano2cnm
    syl
    #
    @48
    1cnd
    #
    adddid
    eqtrd
    oveq1d
    @48
    @62
    @54
    @60
    c1
    cmin
    co
    #
    caddc
    co
    @55
    @48
    @54
    @60
    c1
    @48
    c2
    @53
    @63
    @71
    mulcld
    #
    @60
    cc
    wcel
    @48
    c2
    c1
    2cn
    ax-1cn
    mulcli
    a1i
    @72
    addsubassd
    @48
    @73
    c1
    @54
    caddc
    @73
    c1
    wceq
    @48
    @73
    @20
    c1
    @60
    c2
    c1
    cmin
    2t1e2
    oveq1i
    2m1e1
    eqtri
    a1i
    oveq2d
    eqtrd
    3eqtrd
    ad2antlr
    sylan9eqr
    eqeq1d
    @50
    @56
    @13
    wi
    @41
    @50
    @56
    @10
    c1
    cmin
    co
    #
    @54
    wceq
    #
    @13
    @50
    @10
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @54
    cc
    wcel
    #
    w3a
    #
    @76
    @56
    wb
    @49
    @80
    @6
    @49
    @77
    @78
    @79
    @4
    @77
    @48
    @4
    @10
    @4
    cP
    cM
    @1
    @2
    @27
    @3
    @30
    3ad2ant1
    #
    @2
    @1
    cM
    cn0
    wcel
    @3
    cM
    nnnn0
    3ad2ant2
    #
    nn0expcld
    nn0cnd
    adantr
    @49
    1cnd
    @48
    @79
    @4
    @74
    adantl
    3jca
    adantr
    @10
    c1
    @54
    subadd2
    syl
    @50
    @76
    cP
    c1
    cmin
    co
    #
    cc0
    cM
    c1
    cmin
    co
    #
    cfz
    co
    #
    cP
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cmul
    co
    #
    @54
    wceq
    #
    @13
    @49
    @76
    @90
    wb
    @6
    @49
    @75
    @89
    @54
    @4
    @75
    @89
    wceq
    @48
    @4
    cP
    vk
    cM
    @1
    @2
    cP
    cc
    wcel
    #
    @3
    @1
    @25
    @26
    @91
    @28
    @29
    cP
    nncn
    3syl
    #
    3ad2ant1
    #
    @82
    pwm1geoser
    adantr
    eqeq1d
    adantr
    @50
    @90
    @89
    c2
    cdiv
    co
    #
    @53
    wceq
    #
    @13
    @50
    @89
    cc
    wcel
    @70
    @22
    c2
    cc0
    wne
    wa
    #
    @95
    @90
    wb
    @50
    @83
    @88
    @50
    cP
    c1
    @4
    @91
    @48
    @6
    @93
    ad2antrr
    @50
    1cnd
    #
    subcld
    #
    @4
    @88
    cc
    wcel
    #
    @48
    @6
    @4
    @88
    @4
    @85
    @87
    vk
    @4
    cc0
    @84
    fzfid
    @4
    @86
    @85
    wcel
    #
    wa
    #
    @87
    @101
    cP
    @86
    @4
    @27
    @100
    @81
    adantr
    @100
    @86
    cn0
    wcel
    #
    @4
    @86
    @84
    elfznn0
    #
    adantl
    nn0expcld
    nn0zd
    #
    fsumzcl
    zcnd
    ad2antrr
    #
    mulcld
    @50
    @52
    c1
    @48
    @69
    @4
    @6
    @67
    ad2antlr
    @97
    subcld
    @50
    c2
    c2
    crp
    wcel
    @50
    2rp
    a1i
    rpcnne0d
    #
    @89
    @53
    c2
    divmul2
    syl3anc
    @50
    @95
    @83
    c2
    cdiv
    co
    #
    @88
    cmul
    co
    #
    @53
    wceq
    #
    @13
    @50
    @94
    @108
    @53
    @50
    @83
    cc
    wcel
    @99
    @96
    @94
    @108
    wceq
    @98
    @105
    @106
    @83
    @88
    c2
    div23
    syl3anc
    eqeq1d
    @50
    @109
    c2
    @53
    cdvds
    wbr
    #
    wn
    #
    @13
    @48
    @111
    @4
    @6
    @48
    c2
    @52
    cdvds
    wbr
    #
    wn
    #
    @110
    @48
    @112
    @48
    c2
    cz
    wcel
    @39
    cn
    wcel
    @112
    @48
    c2
    @64
    nn0zd
    @48
    c2
    @38
    c2
    cn
    wcel
    @48
    2nn
    a1i
    @48
    id
    nnmulcld
    c2
    @39
    iddvdsexp
    syl2anc
    notnotd
    @48
    @52
    cz
    wcel
    @113
    @110
    wb
    @48
    @52
    @66
    nn0zd
    @52
    oddm1even
    syl
    mtbid
    ad2antlr
    @50
    @109
    @111
    @13
    wi
    @50
    @109
    wa
    @111
    c2
    @108
    cdvds
    wbr
    #
    wn
    #
    @13
    @109
    @115
    @111
    wb
    @50
    @109
    @114
    @110
    @108
    @53
    c2
    cdvds
    breq2
    notbid
    adantl
    @50
    @115
    @13
    wi
    @109
    @50
    @114
    @13
    @50
    @114
    c2
    @107
    cdvds
    wbr
    #
    c2
    @88
    cdvds
    wbr
    #
    wo
    #
    @50
    @117
    @116
    @50
    @85
    @87
    vk
    @50
    cc0
    @84
    fzfid
    @4
    @100
    @87
    cz
    wcel
    @48
    @6
    @104
    ad4ant14
    @50
    @100
    c2
    @87
    cdvds
    wbr
    #
    wn
    #
    @4
    @100
    @120
    wi
    #
    @48
    @6
    @1
    @2
    @121
    @3
    @102
    @1
    @120
    @100
    @102
    @86
    cn
    wcel
    #
    @86
    cc0
    wceq
    #
    wo
    @1
    @120
    wi
    #
    @86
    elnn0
    @122
    @124
    @123
    @122
    @1
    @120
    @122
    @1
    wa
    #
    @119
    c2
    cP
    wceq
    #
    @125
    c2
    cP
    @1
    c2
    cP
    wne
    #
    @122
    @1
    @25
    cP
    c2
    wne
    #
    wa
    #
    @127
    cP
    cprime
    c2
    eldifsn
    @129
    cP
    c2
    @25
    @128
    simpr
    necomd
    sylbi
    adantl
    neneqd
    c2
    cprime
    wcel
    #
    @125
    @25
    @122
    @119
    @126
    wb
    2prm
    @1
    @25
    @122
    @28
    adantl
    @122
    @1
    simpl
    c2
    cP
    @86
    prmdvdsexpb
    mp3an2i
    mtbird
    ex
    @123
    @1
    @120
    @123
    @1
    wa
    #
    @119
    c2
    c1
    cdvds
    wbr
    n2dvds1
    @131
    @87
    c1
    c2
    cdvds
    @123
    @1
    @87
    cP
    cc0
    cexp
    co
    c1
    @86
    cc0
    cP
    cexp
    oveq2
    @1
    cP
    @92
    exp0d
    sylan9eq
    breq2d
    mtbiri
    ex
    jaoi
    sylbi
    @103
    syl11
    3ad2ant1
    ad2antrr
    imp
    @49
    @6
    c2
    @85
    chash
    cfv
    #
    cdvds
    wbr
    @49
    cM
    @132
    c2
    cdvds
    @4
    cM
    @132
    wceq
    #
    @48
    @2
    @1
    @133
    @3
    @2
    @132
    @84
    c1
    caddc
    co
    #
    cM
    @2
    @84
    cn0
    wcel
    @132
    @134
    wceq
    cM
    nnm1nn0
    @84
    hashfz0
    syl
    @2
    cM
    c1
    cM
    nncn
    @2
    1cnd
    npcand
    eqtr2d
    3ad2ant2
    adantr
    breq2d
    biimpa
    evensumodd
    olcd
    @4
    @114
    @118
    wb
    #
    @48
    @6
    @4
    @130
    @107
    cz
    wcel
    #
    @88
    cz
    wcel
    #
    w3a
    #
    @135
    @1
    @2
    @138
    @3
    @16
    @130
    @136
    @137
    @130
    @16
    2prm
    a1i
    @1
    @136
    @2
    @1
    c2
    cP
    cdvds
    wbr
    wn
    #
    @136
    cP
    oddn2prm
    @1
    @24
    @139
    @136
    wb
    @31
    cP
    oddm1d2
    syl
    mpbid
    adantr
    @16
    @85
    @87
    vk
    @16
    cc0
    @84
    fzfid
    @16
    @100
    wa
    #
    @87
    @140
    cP
    @86
    @1
    @27
    @2
    @100
    @30
    ad2antrr
    @100
    @102
    @16
    @103
    adantl
    nn0expcld
    nn0zd
    fsumzcl
    3jca
    3adant3
    c2
    @107
    @88
    euclemma
    syl
    ad2antrr
    mpbird
    pm2.24d
    adantr
    sylbird
    ex
    mpid
    sylbid
    sylbird
    sylbid
    sylbird
    adantr
    sylbid
    exp31
    com23
    rexlimdva
    com34
    adantr
    sylbid
    com24
    ex
    com25
    impd
    3imp
    pm2.61d
end
