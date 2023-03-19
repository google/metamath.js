include "cr.mm"
include "wcel.mm"
include "c8.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "ceu.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "cppi.mm"
include "crp.mm"
include "2rp.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "1re.mm"
include "2re.mm"
include "ere.mm"
include "remulcli.mm"
include "2pos.mm"
include "epos.mm"
include "mulgt0ii.mm"
include "gt0ne0ii.mm"
include "redivcli.mm"
include "resubcli.mm"
include "2ne0.mm"
include "a1i.mm"
include "cn.mm"
include "8re.mm"
include "simpl.mm"
include "2lt8.mm"
include "ltleii.mm"
include "simpr.mm"
include "letrd.mm"
include "ppinncl.mm"
include "syldan.mm"
include "nnred.mm"
include "cfl.mm"
include "cz.mm"
include "rehalfcl.mm"
include "adantr.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "zred.mm"
include "remulcl.mm"
include "sylancr.mm"
include "clt.mm"
include "1lt2.mm"
include "2t1e2.mm"
include "c4.mm"
include "cuz.mm"
include "4nn.mm"
include "4z.mm"
include "4t2e8.mm"
include "syl5eqbr.mm"
include "cc0.mm"
include "wb.mm"
include "4re.mm"
include "lemuldiv.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "flge.mm"
include "sylancl.mm"
include "syl6breqr.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eluznn.mm"
include "nnge1d.mm"
include "lemul2.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "rplogcld.mm"
include "rpred.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "nndivred.mm"
include "remulcld.mm"
include "syl.mm"
include "0red.mm"
include "8pos.mm"
include "elrpd.mm"
include "relogcld.mm"
include "rerpdivcld.mm"
include "syl2anc.mm"
include "cexp.mm"
include "4pos.mm"
include "elrpii.mm"
include "rpexpcl.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "epr.mm"
include "rerpdivcl.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpri.mm"
include "3lt4.mm"
include "3re.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltled.mm"
include "leidi.mm"
include "logdivlt.mm"
include "mpanl12.mm"
include "loge.mm"
include "oveq1i.mm"
include "syl6breq.mm"
include "pm3.2i.mm"
include "nngt0d.mm"
include "jca.mm"
include "lt2mul2div.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "ltmuldiv.mm"
include "syl3anc.mm"
include "ltsub2dd.mm"
include "cc.mm"
include "recni.mm"
include "rpcnd.mm"
include "subdird.mm"
include "mulcomd.mm"
include "wceq.mm"
include "2z.mm"
include "zmulcl.mm"
include "relogexp.mm"
include "2cnd.mm"
include "nnnn0d.mm"
include "cn0.mm"
include "2nn0.mm"
include "expmuld.mm"
include "sq2.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"
include "wne.mm"
include "divrec2d.mm"
include "divcan5d.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "relogdivd.mm"
include "3brtr4d.mm"
include "cbc.mm"
include "cif.mm"
include "eqid.mm"
include "chebbnd1lem1.mm"
include "lttrd.mm"
include "ltmuldivd.mm"
include "rpcnne0d.mm"
include "divass.mm"
include "flle.mm"
include "lemuldiv2.mm"
include "ppiwordi.mm"
include "lemul1d.mm"
include "ltdiv1.mm"
include "chebbnd1lem2.mm"
include "ltmul2.mm"
include "mul12d.mm"
include "ltdivmul.mm"

theorem chebbnd1lem3
  let cM: class M
  let cN: class N
  assume chebbnd1lem2.1: |- M = ( |_ ` ( N / 2 ) )


  assert |- ( ( N e. RR /\ 8 <_ N ) -> ( ( ( log ` 2 ) - ( 1 / ( 2 x. _e ) ) ) / 2 ) < ( ( ppi ` N ) x. ( ( log ` N ) / N ) ) )

  proof
    cN
    cr
    wcel
    #
    c8
    cN
    cle
    wbr
    #
    wa
    #
    c2
    clog
    cfv
    #
    c1
    c2
    ceu
    cmul
    co
    #
    cdiv
    co
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cN
    cppi
    cfv
    #
    c2
    cM
    cmul
    co
    #
    clog
    cfv
    #
    @9
    cdiv
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @8
    cN
    clog
    cfv
    #
    cN
    cdiv
    co
    #
    cmul
    co
    #
    @7
    cr
    wcel
    @2
    @6
    c2
    @3
    @5
    c2
    crp
    wcel
    #
    @3
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    #
    c1
    @4
    1re
    c2
    ceu
    2re
    ere
    remulcli
    #
    @4
    @19
    c2
    ceu
    2re
    ere
    2pos
    epos
    mulgt0ii
    gt0ne0ii
    #
    redivcli
    #
    resubcli
    #
    2re
    2ne0
    redivcli
    a1i
    @2
    @12
    cr
    wcel
    #
    @13
    cr
    wcel
    @2
    @8
    @11
    @2
    @8
    @0
    @1
    c2
    cN
    cle
    wbr
    @8
    cn
    wcel
    @2
    c2
    c8
    cN
    c2
    cr
    wcel
    #
    @2
    2re
    a1i
    #
    c8
    cr
    wcel
    @2
    8re
    a1i
    #
    @0
    @1
    simpl
    #
    c2
    c8
    cle
    wbr
    @2
    c2
    c8
    2re
    8re
    2lt8
    ltleii
    a1i
    @0
    @1
    simpr
    #
    letrd
    cN
    ppinncl
    syldan
    #
    nnred
    #
    @2
    @10
    @9
    @2
    @10
    @2
    @9
    @2
    @24
    cM
    cr
    wcel
    #
    @9
    cr
    wcel
    #
    2re
    @2
    cM
    @2
    cM
    cN
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    chebbnd1lem2.1
    @2
    @33
    @0
    @33
    cr
    wcel
    #
    @1
    cN
    rehalfcl
    adantr
    #
    flcld
    syl5eqel
    #
    zred
    #
    c2
    cM
    remulcl
    sylancr
    #
    @2
    c1
    c2
    @9
    c1
    cr
    wcel
    #
    @2
    1re
    a1i
    #
    @25
    @39
    c1
    c2
    clt
    wbr
    @2
    1lt2
    a1i
    @2
    c2
    c2
    c1
    cmul
    co
    #
    @9
    cle
    2t1e2
    @2
    c1
    cM
    cle
    wbr
    #
    @42
    @9
    cle
    wbr
    #
    @2
    cM
    @2
    c4
    cn
    wcel
    cM
    c4
    cuz
    cfv
    wcel
    #
    cM
    cn
    wcel
    #
    4nn
    @2
    c4
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    c4
    cM
    cle
    wbr
    @45
    @47
    @2
    4z
    a1i
    @37
    @2
    c4
    @34
    cM
    cle
    @2
    c4
    @33
    cle
    wbr
    #
    c4
    @34
    cle
    wbr
    #
    @2
    c4
    c2
    cmul
    co
    #
    cN
    cle
    wbr
    #
    @49
    @2
    @51
    c8
    cN
    cle
    4t2e8
    @28
    syl5eqbr
    @2
    c4
    cr
    wcel
    #
    @0
    @24
    cc0
    c2
    clt
    wbr
    #
    @52
    @49
    wb
    @53
    @2
    4re
    a1i
    #
    @27
    @25
    @54
    @2
    2pos
    a1i
    #
    c4
    cN
    c2
    lemuldiv
    syl112anc
    mpbid
    @2
    @35
    @47
    @49
    @50
    wb
    @36
    4z
    @33
    c4
    flge
    sylancl
    mpbid
    chebbnd1lem2.1
    syl6breqr
    #
    c4
    cM
    eluz2
    syl3anbrc
    #
    cM
    c4
    eluznn
    sylancr
    #
    nnge1d
    @2
    @40
    @31
    @24
    @54
    @43
    @44
    wb
    @41
    @38
    @25
    @56
    c1
    cM
    c2
    lemul2
    syl112anc
    mpbid
    syl5eqbrr
    #
    ltletrd
    rplogcld
    #
    rpred
    #
    @2
    c2
    cn
    wcel
    @46
    @9
    cn
    wcel
    2nn
    @59
    c2
    cM
    nnmulcl
    sylancr
    #
    nndivred
    #
    remulcld
    #
    @12
    rehalfcl
    syl
    @2
    @8
    @15
    @30
    @2
    @14
    cN
    @2
    cN
    @2
    cN
    @27
    @2
    cc0
    c8
    cN
    @2
    0red
    @26
    @27
    cc0
    c8
    clt
    wbr
    @2
    8pos
    a1i
    @28
    ltletrd
    elrpd
    #
    relogcld
    @66
    rerpdivcld
    #
    remulcld
    #
    @2
    @6
    @12
    clt
    wbr
    #
    @7
    @13
    clt
    wbr
    #
    @2
    @6
    @9
    cppi
    cfv
    #
    @11
    cmul
    co
    #
    @12
    @6
    cr
    wcel
    #
    @2
    @22
    a1i
    #
    @2
    @71
    @11
    @2
    @71
    @2
    @32
    c2
    @9
    cle
    wbr
    @71
    cn
    wcel
    @39
    @60
    @9
    ppinncl
    syl2anc
    nnred
    #
    @64
    remulcld
    @65
    @2
    @6
    @71
    @10
    cmul
    co
    #
    @9
    cdiv
    co
    #
    @72
    clt
    @2
    @6
    @9
    cmul
    co
    #
    @76
    clt
    wbr
    @6
    @77
    clt
    wbr
    @2
    @78
    c4
    cM
    cexp
    co
    #
    cM
    cdiv
    co
    #
    clog
    cfv
    #
    @76
    @2
    @73
    @32
    @78
    cr
    wcel
    @22
    @39
    @6
    @9
    remulcl
    sylancr
    @2
    @80
    @2
    @79
    cM
    @2
    c4
    crp
    wcel
    @48
    @79
    crp
    wcel
    c4
    4re
    4pos
    elrpii
    @37
    c4
    cM
    rpexpcl
    sylancr
    #
    @2
    cM
    @59
    nnrpd
    #
    rpdivcld
    relogcld
    @2
    @71
    @10
    @75
    @62
    remulcld
    #
    @2
    @79
    clog
    cfv
    #
    cM
    ceu
    cdiv
    co
    #
    cmin
    co
    #
    @85
    cM
    clog
    cfv
    #
    cmin
    co
    @78
    @81
    clt
    @2
    @88
    @86
    @85
    @2
    cM
    @83
    relogcld
    #
    @2
    @31
    ceu
    crp
    wcel
    @86
    cr
    wcel
    @38
    epr
    cM
    ceu
    rerpdivcl
    sylancl
    @2
    @79
    @82
    relogcld
    @2
    @88
    ceu
    cmul
    co
    #
    cM
    clt
    wbr
    #
    @88
    @86
    clt
    wbr
    #
    @2
    @90
    c1
    cM
    cmul
    co
    #
    cM
    clt
    @2
    @90
    @93
    clt
    wbr
    #
    @88
    cM
    cdiv
    co
    #
    c1
    ceu
    cdiv
    co
    #
    clt
    wbr
    #
    @2
    @95
    ceu
    clog
    cfv
    #
    ceu
    cdiv
    co
    #
    @96
    clt
    @2
    ceu
    cM
    clt
    wbr
    #
    @95
    @99
    clt
    wbr
    #
    @2
    ceu
    c4
    cM
    ceu
    cr
    wcel
    #
    @2
    ere
    a1i
    #
    @55
    @38
    ceu
    c4
    clt
    wbr
    #
    @2
    ceu
    c3
    clt
    wbr
    #
    c3
    c4
    clt
    wbr
    @104
    c2
    ceu
    clt
    wbr
    @105
    egt2lt3
    simpri
    3lt4
    ceu
    c3
    c4
    ere
    3re
    4re
    lttri
    mp2an
    a1i
    @57
    ltletrd
    #
    @2
    @31
    ceu
    cM
    cle
    wbr
    #
    @100
    @101
    wb
    #
    @38
    @2
    ceu
    cM
    @103
    @38
    @106
    ltled
    @102
    ceu
    ceu
    cle
    wbr
    @31
    @107
    wa
    @108
    ere
    ceu
    ere
    leidi
    ceu
    cM
    logdivlt
    mpanl12
    syl2anc
    mpbid
    @98
    c1
    ceu
    cdiv
    loge
    oveq1i
    syl6breq
    @2
    @88
    cr
    wcel
    #
    @102
    cc0
    ceu
    clt
    wbr
    #
    wa
    #
    @40
    @31
    cc0
    cM
    clt
    wbr
    #
    wa
    @94
    @97
    wb
    @89
    @111
    @2
    @102
    @110
    ere
    epos
    pm3.2i
    a1i
    #
    @41
    @2
    @31
    @112
    @38
    @2
    cM
    @59
    nngt0d
    jca
    @88
    ceu
    c1
    cM
    lt2mul2div
    syl22anc
    mpbird
    @2
    cM
    @2
    cM
    @38
    recnd
    #
    mulid2d
    breqtrd
    @2
    @109
    @31
    @111
    @91
    @92
    wb
    @89
    @38
    @113
    @88
    cM
    ceu
    ltmuldiv
    syl3anc
    mpbid
    ltsub2dd
    @2
    @78
    @3
    @9
    cmul
    co
    #
    @5
    @9
    cmul
    co
    #
    cmin
    co
    @87
    @2
    @3
    @5
    @9
    @3
    cc
    wcel
    @2
    @3
    @18
    recni
    a1i
    #
    @5
    cc
    wcel
    @2
    @5
    @21
    recni
    a1i
    @2
    @9
    @2
    @9
    @63
    nnrpd
    #
    rpcnd
    #
    subdird
    @2
    @115
    @85
    @116
    @86
    cmin
    @2
    @115
    @9
    @3
    cmul
    co
    #
    c2
    @9
    cexp
    co
    #
    clog
    cfv
    #
    @85
    @2
    @3
    @9
    @117
    @119
    mulcomd
    @2
    @17
    @9
    cz
    wcel
    #
    @122
    @120
    wceq
    2rp
    @2
    c2
    cz
    wcel
    @48
    @123
    2z
    @37
    c2
    cM
    zmulcl
    sylancr
    c2
    @9
    relogexp
    sylancr
    @2
    @121
    @79
    clog
    @2
    @121
    c2
    c2
    cexp
    co
    #
    cM
    cexp
    co
    @79
    @2
    c2
    c2
    cM
    @2
    2cnd
    #
    @2
    cM
    @59
    nnnn0d
    c2
    cn0
    wcel
    @2
    2nn0
    a1i
    expmuld
    @124
    c4
    cM
    cexp
    sq2
    oveq1i
    syl6eq
    fveq2d
    3eqtr2d
    @2
    @9
    @4
    cdiv
    co
    @116
    @86
    @2
    @9
    @4
    @119
    @4
    cc
    wcel
    @2
    @4
    @19
    recni
    a1i
    @4
    cc0
    wne
    @2
    @20
    a1i
    divrec2d
    @2
    cM
    ceu
    c2
    @114
    ceu
    cc
    wcel
    @2
    ceu
    ere
    recni
    a1i
    @125
    ceu
    cc0
    wne
    @2
    ceu
    ere
    epos
    gt0ne0ii
    a1i
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    divcan5d
    eqtr3d
    oveq12d
    eqtrd
    @2
    @79
    cM
    @82
    @83
    relogdivd
    3brtr4d
    @2
    @45
    @81
    @76
    clt
    wbr
    @58
    @9
    @9
    cM
    cbc
    co
    #
    cle
    wbr
    @9
    @126
    cif
    #
    cM
    @127
    eqid
    chebbnd1lem1
    syl
    lttrd
    @2
    @6
    @76
    @9
    @74
    @84
    @118
    ltmuldivd
    mpbid
    @2
    @71
    cc
    wcel
    @10
    cc
    wcel
    @9
    cc
    wcel
    @9
    cc0
    wne
    wa
    @77
    @72
    wceq
    @2
    @71
    @75
    recnd
    @2
    @10
    @61
    rpcnd
    @2
    @9
    @118
    rpcnne0d
    @71
    @10
    @9
    divass
    syl3anc
    breqtrd
    @2
    @71
    @8
    cle
    wbr
    #
    @72
    @12
    cle
    wbr
    @2
    @32
    @0
    @9
    cN
    cle
    wbr
    #
    @128
    @39
    @27
    @2
    @129
    cM
    @33
    cle
    wbr
    #
    @2
    cM
    @34
    @33
    cle
    chebbnd1lem2.1
    @2
    @35
    @34
    @33
    cle
    wbr
    @36
    @33
    flle
    syl
    syl5eqbr
    @2
    @31
    @0
    @24
    @54
    @129
    @130
    wb
    @38
    @27
    @25
    @56
    cM
    cN
    c2
    lemuldiv2
    syl112anc
    mpbird
    @9
    cN
    ppiwordi
    syl3anc
    @2
    @71
    @8
    @11
    @75
    @30
    @2
    @10
    @9
    @61
    @118
    rpdivcld
    lemul1d
    mpbid
    ltletrd
    @2
    @73
    @23
    @24
    @54
    @69
    @70
    wb
    @74
    @65
    @25
    @56
    @6
    @12
    c2
    ltdiv1
    syl112anc
    mpbid
    @2
    @13
    @16
    clt
    wbr
    #
    @12
    c2
    @16
    cmul
    co
    #
    clt
    wbr
    #
    @2
    @12
    @8
    c2
    @15
    cmul
    co
    #
    cmul
    co
    #
    @132
    clt
    @2
    @11
    @134
    clt
    wbr
    #
    @12
    @135
    clt
    wbr
    #
    cM
    cN
    chebbnd1lem2.1
    chebbnd1lem2
    @2
    @11
    cr
    wcel
    @134
    cr
    wcel
    #
    @8
    cr
    wcel
    cc0
    @8
    clt
    wbr
    @136
    @137
    wb
    @64
    @2
    @24
    @15
    cr
    wcel
    @138
    2re
    @67
    c2
    @15
    remulcl
    sylancr
    @30
    @2
    @8
    @29
    nngt0d
    @11
    @134
    @8
    ltmul2
    syl112anc
    mpbid
    @2
    @8
    c2
    @15
    @2
    @8
    @30
    recnd
    @125
    @2
    @15
    @67
    recnd
    mul12d
    breqtrd
    @2
    @23
    @16
    cr
    wcel
    @24
    @54
    @131
    @133
    wb
    @65
    @68
    @25
    @56
    @12
    @16
    c2
    ltdivmul
    syl112anc
    mpbird
    lttrd
end
