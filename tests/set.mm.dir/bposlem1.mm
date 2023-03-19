include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "cpc.mm"
include "cexp.mm"
include "cle.mm"
include "wbr.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "csu.mm"
include "cc0.mm"
include "cif.mm"
include "fzfid.mm"
include "crp.mm"
include "2nn.mm"
include "nnmulcl.mm"
include "mpan.mm"
include "ad2antrr.mm"
include "prmnn.mm"
include "ad2antlr.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "rpred.mm"
include "flcld.mm"
include "cz.mm"
include "2z.mm"
include "simpll.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "zsubcld.mm"
include "zred.mm"
include "cr.mm"
include "1re.mm"
include "0re.mm"
include "keepel.mm"
include "a1i.mm"
include "caddc.mm"
include "clt.mm"
include "resubcld.mm"
include "2re.mm"
include "flle.mm"
include "syl.mm"
include "lesub1dd.mm"
include "resubcl.mm"
include "sylancl.mm"
include "remulcl.mm"
include "flltp1.mm"
include "1red.mm"
include "ltsubaddd.mm"
include "mpbird.mm"
include "wb.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmul2.mm"
include "mp3an3.mm"
include "mpbid.mm"
include "ltsub2dd.mm"
include "2cnd.mm"
include "cc.mm"
include "nncn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divassd.mm"
include "recnd.mm"
include "1cnd.mm"
include "subdid.mm"
include "2t1e2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "wceq.mm"
include "2cn.mm"
include "nncan.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "lelttrd.mm"
include "df-2.mm"
include "syl6breq.mm"
include "1z.mm"
include "zleltp1.mm"
include "iftrue.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "nnge1d.mm"
include "biantrurd.mm"
include "nnred.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluz2b1.mm"
include "simprbi.mm"
include "jca.mm"
include "adantr.mm"
include "elfzelz.mm"
include "nnrpd.mm"
include "efexple.mm"
include "syl3anc.mm"
include "nnzd.mm"
include "1lt2.mm"
include "nnre.mm"
include "0le2.mm"
include "nnge1.mm"
include "lemul2a.mm"
include "syl31anc.mm"
include "syl5eqbrr.mm"
include "ltletrd.mm"
include "rplogcld.mm"
include "rpdivcld.mm"
include "elfz.mm"
include "3bitr4rd.mm"
include "notbid.mm"
include "ltnled.mm"
include "bitr4d.mm"
include "rpge0d.mm"
include "adantrr.mm"
include "nngt0d.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mulid1d.mm"
include "bitrd.mm"
include "biimprd.mm"
include "impr.mm"
include "0p1e1.mm"
include "syl6breqr.mm"
include "0z.mm"
include "flbi.mm"
include "mpbir2and.mm"
include "ltaddrp2d.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "wi.mm"
include "lttr.mm"
include "mpand.mm"
include "sylibrd.mm"
include "oveq2d.mm"
include "2t0e0.mm"
include "0m0e0.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "expr.mm"
include "sylbid.mm"
include "iffalse.mm"
include "eqcomd.mm"
include "mpbidi.mm"
include "pm2.61d.mm"
include "fsumle.mm"
include "pcbcctr.mm"
include "chash.mm"
include "cfn.mm"
include "wss.mm"
include "ce.mm"
include "cn0.mm"
include "bernneq3.mm"
include "ltled.mm"
include "reeflogd.mm"
include "reexplog.mm"
include "3brtr4d.mm"
include "relogcld.mm"
include "remulcld.mm"
include "efle.mm"
include "ledivmul2d.mm"
include "letrd.mm"
include "eluz.mm"
include "fzss2.mm"
include "sumhash.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "hashfz1.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "simpr.mm"
include "nnnn0.mm"
include "fzctr.mm"
include "bccl2.mm"
include "pccld.mm"
include "nn0zd.mm"
include "syl211anc.mm"

theorem bposlem1
  let cP: class P
  let cN: class N
  let vk: setvar k


  assert |- ( ( N e. NN /\ P e. Prime ) -> ( P ^ ( P pCnt ( ( 2 x. N ) _C N ) ) ) <_ ( 2 x. N ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cprime
    wcel
    #
    wa
    #
    cP
    cP
    c2
    cN
    cmul
    co
    #
    cN
    cbc
    co
    #
    cpc
    co
    #
    cexp
    co
    @3
    cle
    wbr
    #
    @5
    @3
    clog
    cfv
    #
    cP
    clog
    cfv
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cle
    wbr
    #
    @2
    c1
    @3
    cfz
    co
    #
    @3
    cP
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cN
    @14
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    vk
    csu
    @12
    @13
    c1
    @10
    cfz
    co
    #
    wcel
    #
    c1
    cc0
    cif
    #
    vk
    csu
    #
    @5
    @10
    cle
    @2
    @12
    @20
    @23
    vk
    @2
    c1
    @3
    fzfid
    #
    @2
    @13
    @12
    wcel
    #
    wa
    #
    @20
    @27
    @16
    @19
    @27
    @15
    @27
    @15
    @27
    @3
    cn
    wcel
    #
    @14
    cn
    wcel
    #
    @15
    crp
    wcel
    #
    @0
    @28
    @1
    @26
    c2
    cn
    wcel
    @0
    @28
    2nn
    c2
    cN
    nnmulcl
    mpan
    #
    ad2antrr
    @27
    cP
    @13
    @1
    cP
    cn
    wcel
    #
    @0
    @26
    cP
    prmnn
    #
    ad2antlr
    @27
    @13
    @26
    @13
    cn
    wcel
    @2
    @13
    @3
    elfznn
    adantl
    #
    nnnn0d
    nnexpcld
    #
    @28
    @3
    crp
    wcel
    #
    @14
    crp
    wcel
    #
    @30
    @29
    @3
    nnrp
    @14
    nnrp
    #
    @3
    @14
    rpdivcl
    syl2an
    syl2anc
    #
    rpred
    #
    flcld
    #
    @27
    c2
    cz
    wcel
    @18
    cz
    wcel
    @19
    cz
    wcel
    2z
    @27
    @17
    @27
    @17
    @27
    @0
    @29
    @17
    crp
    wcel
    #
    @0
    @1
    @26
    simpll
    @35
    @0
    cN
    crp
    wcel
    @37
    @42
    @29
    cN
    nnrp
    #
    @38
    cN
    @14
    rpdivcl
    syl2an
    syl2anc
    #
    rpred
    #
    flcld
    #
    c2
    @18
    zmulcl
    sylancr
    #
    zsubcld
    #
    zred
    #
    @23
    cr
    wcel
    @27
    @22
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    @27
    @22
    @20
    @23
    cle
    wbr
    #
    @27
    @50
    @22
    @20
    c1
    cle
    wbr
    #
    @27
    @51
    @20
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @27
    @20
    c2
    @52
    clt
    @27
    @20
    @15
    @19
    cmin
    co
    #
    c2
    @49
    @27
    @15
    @19
    @40
    @27
    @19
    @47
    zred
    #
    resubcld
    c2
    cr
    wcel
    #
    @27
    2re
    a1i
    @27
    @16
    @15
    @19
    @27
    @16
    @41
    zred
    @40
    @55
    @27
    @15
    cr
    wcel
    #
    @16
    @15
    cle
    wbr
    @40
    @15
    flle
    syl
    lesub1dd
    @27
    @54
    @15
    c2
    @17
    c1
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    c2
    clt
    @27
    @59
    @19
    @15
    @27
    @56
    @58
    cr
    wcel
    #
    @59
    cr
    wcel
    2re
    @27
    @17
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @61
    @45
    1re
    @17
    c1
    resubcl
    sylancl
    #
    c2
    @58
    remulcl
    sylancr
    @55
    @40
    @27
    @58
    @18
    clt
    wbr
    #
    @59
    @19
    clt
    wbr
    #
    @27
    @65
    @17
    @18
    c1
    caddc
    co
    clt
    wbr
    #
    @27
    @62
    @67
    @45
    @17
    flltp1
    syl
    @27
    @17
    c1
    @18
    @45
    @27
    1red
    #
    @27
    @18
    @46
    zred
    #
    ltsubaddd
    mpbird
    @27
    @61
    @18
    cr
    wcel
    #
    @65
    @66
    wb
    #
    @64
    @69
    @61
    @70
    @56
    cc0
    c2
    clt
    wbr
    #
    wa
    @71
    @56
    @72
    2re
    2pos
    pm3.2i
    @58
    @18
    c2
    ltmul2
    mp3an3
    syl2anc
    mpbid
    ltsub2dd
    @27
    @60
    c2
    @17
    cmul
    co
    #
    @73
    c2
    cmin
    co
    #
    cmin
    co
    #
    c2
    @27
    @15
    @73
    @59
    @74
    cmin
    @27
    c2
    cN
    @14
    @27
    2cnd
    #
    @0
    cN
    cc
    wcel
    @1
    @26
    cN
    nncn
    #
    ad2antrr
    @27
    @14
    @35
    nncnd
    #
    @27
    @14
    @35
    nnne0d
    divassd
    @27
    @59
    @73
    c2
    c1
    cmul
    co
    #
    cmin
    co
    @74
    @27
    c2
    @17
    c1
    @76
    @27
    @17
    @45
    recnd
    @27
    1cnd
    subdid
    @79
    c2
    @73
    cmin
    2t1e2
    oveq2i
    syl6eq
    oveq12d
    @27
    @73
    cc
    wcel
    c2
    cc
    wcel
    @75
    c2
    wceq
    @27
    @73
    @27
    @56
    @62
    @73
    cr
    wcel
    2re
    @45
    c2
    @17
    remulcl
    sylancr
    recnd
    2cn
    @73
    c2
    nncan
    sylancl
    eqtrd
    breqtrd
    lelttrd
    df-2
    syl6breq
    @27
    @20
    cz
    wcel
    c1
    cz
    wcel
    #
    @51
    @53
    wb
    @48
    1z
    @20
    c1
    zleltp1
    sylancl
    mpbird
    @22
    @23
    c1
    @20
    cle
    @22
    c1
    cc0
    iftrue
    breq2d
    syl5ibrcom
    @22
    wn
    #
    @20
    cc0
    cle
    wbr
    #
    @50
    @27
    @27
    @81
    @3
    @14
    clt
    wbr
    #
    @82
    @27
    @81
    @14
    @3
    cle
    wbr
    #
    wn
    @83
    @27
    @22
    @84
    @27
    @13
    @10
    cle
    wbr
    #
    c1
    @13
    cle
    wbr
    #
    @85
    wa
    #
    @84
    @22
    @27
    @86
    @85
    @27
    @13
    @34
    nnge1d
    biantrurd
    @27
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @13
    cz
    wcel
    #
    @36
    @84
    @85
    wb
    @2
    @90
    @26
    @2
    @88
    @89
    @2
    cP
    @1
    @32
    @0
    @33
    adantl
    #
    nnred
    #
    @2
    cP
    c2
    cuz
    cfv
    wcel
    #
    @89
    @1
    @94
    @0
    cP
    prmuz2
    adantl
    #
    @94
    cP
    cz
    wcel
    @89
    cP
    eluz2b1
    simprbi
    syl
    #
    jca
    adantr
    @26
    @91
    @2
    @13
    c1
    @3
    elfzelz
    adantl
    @2
    @36
    @26
    @2
    @3
    @0
    @28
    @1
    @31
    adantr
    #
    nnrpd
    #
    adantr
    cP
    @3
    @13
    efexple
    syl3anc
    @27
    @91
    @80
    @10
    cz
    wcel
    #
    @22
    @87
    wb
    @27
    @13
    @34
    nnzd
    @80
    @27
    1z
    a1i
    @2
    @99
    @26
    @2
    @9
    @2
    @9
    @2
    @7
    @8
    @2
    @3
    @2
    @3
    @97
    nnred
    #
    @2
    c1
    c2
    @3
    @2
    1red
    #
    @56
    @2
    2re
    a1i
    @100
    c1
    c2
    clt
    wbr
    @2
    1lt2
    a1i
    @2
    c2
    @79
    @3
    cle
    2t1e2
    @2
    @63
    cN
    cr
    wcel
    #
    @56
    cc0
    c2
    cle
    wbr
    #
    wa
    #
    c1
    cN
    cle
    wbr
    #
    @79
    @3
    cle
    wbr
    @101
    @0
    @102
    @1
    cN
    nnre
    #
    adantr
    @104
    @2
    @56
    @103
    2re
    0le2
    pm3.2i
    a1i
    @0
    @105
    @1
    cN
    nnge1
    adantr
    c1
    cN
    c2
    lemul2a
    syl31anc
    syl5eqbrr
    ltletrd
    rplogcld
    @2
    cP
    @93
    @96
    rplogcld
    #
    rpdivcld
    #
    rpred
    #
    flcld
    #
    adantr
    @13
    c1
    @10
    elfz
    syl3anc
    3bitr4rd
    notbid
    @27
    @3
    @14
    @2
    @3
    cr
    wcel
    #
    @26
    @100
    adantr
    #
    @27
    @14
    @35
    nnred
    #
    ltnled
    bitr4d
    @2
    @26
    @83
    @82
    @2
    @26
    @83
    wa
    wa
    #
    @20
    cc0
    cc0
    cle
    @114
    @20
    cc0
    cc0
    cmin
    co
    cc0
    @114
    @16
    cc0
    @19
    cc0
    cmin
    @114
    @16
    cc0
    wceq
    #
    cc0
    @15
    cle
    wbr
    #
    @15
    cc0
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @2
    @26
    @116
    @83
    @27
    @15
    @39
    rpge0d
    adantrr
    @114
    @15
    c1
    @117
    clt
    @2
    @26
    @83
    @15
    c1
    clt
    wbr
    #
    @27
    @119
    @83
    @27
    @119
    @3
    @14
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @83
    @27
    @111
    @63
    @14
    cr
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    @119
    @121
    wb
    @112
    @68
    @113
    @27
    @14
    @35
    nngt0d
    #
    @3
    c1
    @14
    ltdivmul
    syl112anc
    @27
    @120
    @14
    @3
    clt
    @27
    @14
    @78
    mulid1d
    #
    breq2d
    bitrd
    biimprd
    impr
    0p1e1
    syl6breqr
    @114
    @57
    cc0
    cz
    wcel
    #
    @115
    @116
    @118
    wa
    wb
    @2
    @26
    @57
    @83
    @40
    adantrr
    0z
    @15
    cc0
    flbi
    sylancl
    mpbir2and
    @114
    @19
    c2
    cc0
    cmul
    co
    cc0
    @114
    @18
    cc0
    c2
    cmul
    @114
    @18
    cc0
    wceq
    #
    cc0
    @17
    cle
    wbr
    #
    @17
    @117
    clt
    wbr
    #
    @2
    @26
    @128
    @83
    @27
    @17
    @44
    rpge0d
    adantrr
    @114
    @17
    c1
    @117
    clt
    @2
    @26
    @83
    @17
    c1
    clt
    wbr
    #
    @27
    @83
    cN
    @14
    clt
    wbr
    #
    @130
    @27
    cN
    @3
    clt
    wbr
    #
    @83
    @131
    @0
    @132
    @1
    @26
    @0
    cN
    cN
    cN
    caddc
    co
    @3
    clt
    @0
    cN
    cN
    @106
    @43
    ltaddrp2d
    @0
    cN
    @77
    2timesd
    breqtrrd
    ad2antrr
    @27
    @102
    @111
    @122
    @132
    @83
    wa
    @131
    wi
    @0
    @102
    @1
    @26
    @106
    ad2antrr
    #
    @112
    @113
    cN
    @3
    @14
    lttr
    syl3anc
    mpand
    @27
    @130
    cN
    @120
    clt
    wbr
    #
    @131
    @27
    @102
    @63
    @122
    @123
    @130
    @134
    wb
    @133
    @68
    @113
    @124
    cN
    c1
    @14
    ltdivmul
    syl112anc
    @27
    @120
    @14
    cN
    clt
    @125
    breq2d
    bitrd
    sylibrd
    impr
    0p1e1
    syl6breqr
    @114
    @62
    @126
    @127
    @128
    @129
    wa
    wb
    @2
    @26
    @62
    @83
    @45
    adantrr
    0z
    @17
    cc0
    flbi
    sylancl
    mpbir2and
    oveq2d
    2t0e0
    syl6eq
    oveq12d
    0m0e0
    syl6eq
    0le0
    syl6eqbr
    expr
    sylbid
    @81
    cc0
    @23
    @20
    cle
    @81
    @23
    cc0
    @22
    c1
    cc0
    iffalse
    eqcomd
    breq2d
    mpbidi
    pm2.61d
    fsumle
    cP
    vk
    cN
    pcbcctr
    @2
    @24
    @21
    chash
    cfv
    #
    @10
    @2
    @12
    cfn
    wcel
    @21
    @12
    wss
    #
    @24
    @135
    wceq
    @25
    @2
    @3
    @10
    cuz
    cfv
    wcel
    #
    @136
    @2
    @137
    @10
    @3
    cle
    wbr
    #
    @2
    @10
    @9
    @3
    @2
    @10
    @110
    zred
    @109
    @100
    @2
    @9
    cr
    wcel
    #
    @10
    @9
    cle
    wbr
    @109
    @9
    flle
    syl
    @2
    @9
    @3
    cle
    wbr
    @7
    @3
    @8
    cmul
    co
    #
    cle
    wbr
    #
    @2
    @141
    @7
    ce
    cfv
    #
    @140
    ce
    cfv
    #
    cle
    wbr
    #
    @2
    @3
    cP
    @3
    cexp
    co
    #
    @142
    @143
    cle
    @2
    @3
    @145
    @100
    @2
    @145
    @2
    cP
    @3
    @92
    @2
    @3
    @97
    nnnn0d
    #
    nnexpcld
    nnred
    @2
    @94
    @3
    cn0
    wcel
    @3
    @145
    clt
    wbr
    @95
    @146
    cP
    @3
    bernneq3
    syl2anc
    ltled
    @2
    @3
    @98
    reeflogd
    @2
    @145
    @143
    @2
    cP
    crp
    wcel
    @3
    cz
    wcel
    #
    @145
    @143
    wceq
    @2
    cP
    @92
    nnrpd
    @2
    @3
    @97
    nnzd
    #
    cP
    @3
    reexplog
    syl2anc
    eqcomd
    3brtr4d
    @2
    @7
    cr
    wcel
    @140
    cr
    wcel
    @141
    @144
    wb
    @2
    @3
    @98
    relogcld
    #
    @2
    @3
    @8
    @100
    @2
    @8
    @107
    rpred
    remulcld
    @7
    @140
    efle
    syl2anc
    mpbird
    @2
    @7
    @3
    @8
    @149
    @100
    @107
    ledivmul2d
    mpbird
    letrd
    @2
    @99
    @147
    @137
    @138
    wb
    @110
    @148
    @10
    @3
    eluz
    syl2anc
    mpbird
    @10
    c1
    @3
    fzss2
    syl
    @21
    @12
    vk
    sumhash
    syl2anc
    @2
    @139
    cc0
    @9
    cle
    wbr
    wa
    @10
    cn0
    wcel
    @135
    @10
    wceq
    @2
    @9
    @108
    rprege0d
    @9
    flge0nn0
    @10
    hashfz1
    3syl
    eqtr2d
    3brtr4d
    @2
    @88
    @89
    @5
    cz
    wcel
    @36
    @6
    @11
    wb
    @93
    @96
    @2
    @5
    @2
    cP
    @4
    @0
    @1
    simpr
    @0
    @4
    cn
    wcel
    #
    @1
    @0
    cN
    cn0
    wcel
    cN
    cc0
    @3
    cfz
    co
    wcel
    @150
    cN
    nnnn0
    cN
    fzctr
    cN
    @3
    bccl2
    3syl
    adantr
    pccld
    nn0zd
    @98
    cP
    @3
    @5
    efexple
    syl211anc
    mpbird
end
