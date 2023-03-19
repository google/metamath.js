include "cc0.mm"
include "c1.mm"
include "cc.mm"
include "ce.mm"
include "cdv.mm"
include "co.mm"
include "wbr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cnt.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "0cn.mm"
include "ctop.mm"
include "wceq.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "ntrtop.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "wne.mm"
include "cabs.mm"
include "clt.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ax-1cn.mm"
include "cle.mm"
include "cif.mm"
include "1rp.mm"
include "ifcl.mm"
include "mpan2.mm"
include "eldifsn.mm"
include "simprl.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cr.mm"
include "wb.mm"
include "abscld.mm"
include "rpre.mm"
include "adantr.mm"
include "1red.mm"
include "ltmin.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "simplr.mm"
include "sylibr.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "simplrl.mm"
include "efcl.mm"
include "1cnd.mm"
include "subcld.mm"
include "simplrr.mm"
include "divcld.mm"
include "simpll.mm"
include "rpred.mm"
include "cmul.mm"
include "c2.mm"
include "cexp.mm"
include "c3.mm"
include "c4.mm"
include "abscl.mm"
include "ad2antrr.mm"
include "subcl.mm"
include "sylancl.mm"
include "remulcld.mm"
include "resqcld.mm"
include "cn.mm"
include "3re.mm"
include "4nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "remulcl.mm"
include "caddc.mm"
include "cfa.mm"
include "cuz.mm"
include "cn0.mm"
include "csu.mm"
include "divcan2d.mm"
include "divsubdird.mm"
include "dividd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "subsub4d.mm"
include "df-2.mm"
include "1nn0.mm"
include "1e0p1.mm"
include "0nn0.mm"
include "0cnd.mm"
include "efval2.mm"
include "nn0uz.mm"
include "sumeq1i.mm"
include "syl6req.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "eft0val.mm"
include "syl6eqr.mm"
include "efsep.mm"
include "exp1.mm"
include "fac1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "div1.mm"
include "eqcomd.mm"
include "addcl.mm"
include "sylancr.mm"
include "2nn0.mm"
include "eftlcl.mm"
include "subaddd.mm"
include "mpbird.mm"
include "3eqtr3d.mm"
include "absmuld.mm"
include "eqtr3d.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "ltled.mm"
include "eftlub.mm"
include "eqbrtrrd.mm"
include "df-3.mm"
include "fac2.mm"
include "oveq1i.mm"
include "2t2e4.mm"
include "eqtr2i.mm"
include "oveq12i.mm"
include "syl6breqr.mm"
include "sqge0d.mm"
include "1re.mm"
include "3lt4.mm"
include "4cn.mm"
include "mulid1i.mm"
include "breqtrri.mm"
include "4re.mm"
include "4pos.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "mp3an.mm"
include "mpbir.mm"
include "ltleii.mm"
include "lemul2ad.mm"
include "recnd.mm"
include "sqcld.mm"
include "mulid1d.mm"
include "breqtrd.mm"
include "letrd.mm"
include "sqvald.mm"
include "absgt0.mm"
include "mpbid.mm"
include "elrpd.mm"
include "lemul2d.mm"
include "ad2ant2l.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "adantld.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rgen.mm"
include "wtru.mm"
include "wf.mm"
include "eldifi.mm"
include "eldifsni.mm"
include "fmpti.mm"
include "difssd.mm"
include "ellimc3.mm"
include "trud.mm"
include "mpbir2an.mm"
include "crest.mm"
include "restid.mm"
include "eqcomi.mm"
include "ef0.mm"
include "mpteq2ia.mm"
include "wss.mm"
include "ssid.mm"
include "eff.mm"
include "eldv.mm"

theorem dveflem
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- 0 ( CC _D exp ) 1

  proof
    cc0
    c1
    cc
    ce
    cdv
    co
    wbr
    #
    cc0
    cc
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    wcel
    #
    c1
    vz
    cc
    cc0
    csn
    #
    cdif
    #
    vz
    cv
    #
    ce
    cfv
    #
    c1
    cmin
    co
    #
    @6
    cdiv
    co
    #
    cmpt
    #
    cc0
    climc
    co
    wcel
    #
    cc0
    cc
    @2
    0cn
    @1
    ctop
    wcel
    #
    @2
    cc
    wceq
    @1
    @1
    eqid
    #
    cnfldtop
    #
    @1
    cc
    cc
    @1
    @1
    @13
    cnfldtopon
    toponunii
    #
    ntrtop
    ax-mp
    eleqtrri
    @11
    c1
    cc
    wcel
    #
    vw
    cv
    #
    cc0
    wne
    #
    @17
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    @17
    @10
    cfv
    #
    c1
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    @5
    wral
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    #
    ax-1cn
    @31
    vx
    crp
    @27
    crp
    wcel
    #
    @27
    c1
    cle
    wbr
    #
    @27
    c1
    cif
    #
    crp
    wcel
    #
    @18
    @20
    @35
    clt
    wbr
    #
    wa
    #
    @28
    wi
    #
    vw
    @5
    wral
    #
    @31
    @33
    c1
    crp
    wcel
    @36
    1rp
    @34
    @27
    c1
    crp
    ifcl
    mpan2
    @33
    @39
    vw
    @5
    @17
    @5
    wcel
    #
    @33
    @17
    cc
    wcel
    #
    @18
    wa
    #
    @39
    @17
    cc
    cc0
    eldifsn
    #
    @33
    @43
    wa
    #
    @37
    @28
    @18
    @45
    @37
    @17
    cabs
    cfv
    #
    @27
    clt
    wbr
    #
    @46
    c1
    clt
    wbr
    #
    wa
    #
    @28
    @45
    @37
    @46
    @35
    clt
    wbr
    #
    @49
    @45
    @20
    @46
    @35
    clt
    @45
    @19
    @17
    cabs
    @45
    @17
    @33
    @42
    @18
    simprl
    #
    subid1d
    fveq2d
    breq1d
    @45
    @46
    cr
    wcel
    #
    @27
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @50
    @49
    wb
    @45
    @17
    @51
    abscld
    @33
    @53
    @43
    @27
    rpre
    adantr
    @45
    1red
    @46
    @27
    c1
    ltmin
    syl3anc
    bitrd
    @45
    @49
    @28
    @45
    @49
    wa
    #
    @26
    @17
    ce
    cfv
    #
    c1
    cmin
    co
    #
    @17
    cdiv
    co
    #
    c1
    cmin
    co
    #
    cabs
    cfv
    #
    @27
    clt
    @55
    @25
    @59
    cabs
    @55
    @24
    @58
    c1
    cmin
    @55
    @41
    @24
    @58
    wceq
    @55
    @43
    @41
    @33
    @43
    @49
    simplr
    @44
    sylibr
    vz
    @17
    @9
    @58
    @5
    @10
    @6
    @17
    wceq
    #
    @8
    @57
    @6
    @17
    cdiv
    @61
    @7
    @56
    c1
    cmin
    @6
    @17
    ce
    fveq2
    oveq1d
    @61
    id
    oveq12d
    @10
    eqid
    #
    @57
    @17
    cdiv
    ovex
    fvmpt
    syl
    oveq1d
    fveq2d
    @55
    @60
    @46
    @27
    @55
    @59
    @55
    @58
    c1
    @55
    @57
    @17
    @55
    @56
    c1
    @55
    @42
    @56
    cc
    wcel
    #
    @33
    @42
    @18
    @49
    simplrl
    #
    @17
    efcl
    #
    syl
    @55
    1cnd
    #
    subcld
    @64
    @33
    @42
    @18
    @49
    simplrr
    divcld
    @66
    subcld
    abscld
    @55
    @17
    @64
    abscld
    @55
    @27
    @33
    @43
    @49
    simpll
    rpred
    @43
    @48
    @60
    @46
    cle
    wbr
    #
    @33
    @47
    @43
    @48
    wa
    #
    @67
    @46
    @60
    cmul
    co
    #
    @46
    @46
    cmul
    co
    #
    cle
    wbr
    @68
    @69
    @46
    c2
    cexp
    co
    #
    @70
    cle
    @68
    @69
    @71
    c3
    c4
    cdiv
    co
    #
    cmul
    co
    #
    @71
    @68
    @46
    @60
    @42
    @52
    @18
    @48
    @17
    abscl
    ad2antrr
    #
    @68
    @59
    @68
    @58
    c1
    @68
    @57
    @17
    @68
    @63
    @16
    @57
    cc
    wcel
    @42
    @63
    @18
    @48
    @65
    ad2antrr
    #
    ax-1cn
    @56
    c1
    subcl
    sylancl
    #
    @42
    @18
    @48
    simpll
    #
    @42
    @18
    @48
    simplr
    #
    divcld
    @68
    1cnd
    #
    subcld
    #
    abscld
    #
    remulcld
    @68
    @71
    cr
    wcel
    @72
    cr
    wcel
    #
    @73
    cr
    wcel
    @68
    @46
    @74
    resqcld
    #
    c3
    cr
    wcel
    #
    c4
    cn
    wcel
    @82
    3re
    4nn
    c3
    c4
    nndivre
    mp2an
    #
    @71
    @72
    remulcl
    sylancl
    @83
    @68
    @69
    @71
    c2
    c1
    caddc
    co
    #
    c2
    cfa
    cfv
    #
    c2
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @73
    cle
    @68
    c2
    cuz
    cfv
    vk
    cv
    vn
    cn0
    @17
    vn
    cv
    #
    cexp
    co
    @91
    cfa
    cfv
    #
    cdiv
    co
    cmpt
    #
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    #
    @69
    @90
    cle
    @68
    @17
    @59
    cmul
    co
    #
    cabs
    cfv
    @96
    @69
    @68
    @97
    @95
    cabs
    @68
    @17
    @57
    @17
    cmin
    co
    #
    @17
    cdiv
    co
    #
    cmul
    co
    @98
    @97
    @95
    @68
    @98
    @17
    @68
    @57
    @17
    @76
    @77
    subcld
    @77
    @78
    divcan2d
    @68
    @99
    @59
    @17
    cmul
    @68
    @99
    @58
    @17
    @17
    cdiv
    co
    #
    cmin
    co
    @59
    @68
    @57
    @17
    @17
    @76
    @77
    @77
    @78
    divsubdird
    @68
    @100
    c1
    @58
    cmin
    @68
    @17
    @77
    @78
    dividd
    oveq2d
    eqtrd
    oveq2d
    @68
    @98
    @56
    c1
    @17
    caddc
    co
    #
    cmin
    co
    #
    @95
    @68
    @56
    c1
    @17
    @75
    @79
    @77
    subsub4d
    @68
    @102
    @95
    wceq
    @101
    @95
    caddc
    co
    #
    @56
    wceq
    @68
    @56
    @103
    @68
    @17
    c1
    @101
    vk
    vn
    @93
    c1
    c2
    @93
    eqid
    #
    df-2
    1nn0
    @77
    @79
    @68
    @17
    cc0
    c1
    vk
    vn
    @93
    cc0
    c1
    @104
    1e0p1
    0nn0
    @77
    @68
    0cnd
    @68
    cc0
    cc0
    cuz
    cfv
    #
    @94
    vk
    csu
    #
    caddc
    co
    cc0
    @56
    caddc
    co
    @56
    @68
    @106
    @56
    cc0
    caddc
    @68
    @56
    cn0
    @94
    vk
    csu
    #
    @106
    @42
    @56
    @107
    wceq
    @18
    @48
    @17
    vk
    vn
    @93
    @104
    efval2
    ad2antrr
    cn0
    @105
    @94
    vk
    nn0uz
    sumeq1i
    syl6req
    oveq2d
    @68
    @56
    @75
    addid2d
    eqtr2d
    @68
    cc0
    @17
    cc0
    cexp
    co
    cc0
    cfa
    cfv
    cdiv
    co
    #
    caddc
    co
    cc0
    c1
    caddc
    co
    c1
    @68
    @108
    c1
    cc0
    caddc
    @42
    @108
    c1
    wceq
    @18
    @48
    @17
    eft0val
    ad2antrr
    oveq2d
    1e0p1
    syl6eqr
    efsep
    @68
    @17
    c1
    cexp
    co
    #
    c1
    cfa
    cfv
    #
    cdiv
    co
    #
    @17
    c1
    caddc
    @68
    @111
    @17
    c1
    cdiv
    co
    #
    @17
    @68
    @111
    @17
    @110
    cdiv
    co
    @112
    @68
    @109
    @17
    @110
    cdiv
    @42
    @109
    @17
    wceq
    @18
    @48
    @17
    exp1
    ad2antrr
    oveq1d
    @110
    c1
    @17
    cdiv
    fac1
    oveq2i
    syl6eq
    @42
    @112
    @17
    wceq
    @18
    @48
    @17
    div1
    ad2antrr
    eqtrd
    oveq2d
    efsep
    eqcomd
    @68
    @56
    @101
    @95
    @75
    @68
    @16
    @42
    @101
    cc
    wcel
    ax-1cn
    @77
    c1
    @17
    addcl
    sylancr
    @68
    @42
    c2
    cn0
    wcel
    @95
    cc
    wcel
    @77
    2nn0
    @17
    vk
    vn
    @93
    c2
    @104
    eftlcl
    sylancl
    subaddd
    mpbird
    eqtrd
    3eqtr3d
    fveq2d
    @68
    @17
    @59
    @77
    @80
    absmuld
    eqtr3d
    @68
    @17
    vk
    vn
    @93
    vn
    cn0
    @46
    @91
    cexp
    co
    @92
    cdiv
    co
    cmpt
    #
    vn
    cn0
    @71
    @87
    cdiv
    co
    c1
    @86
    cdiv
    co
    @91
    cexp
    co
    cmul
    co
    cmpt
    #
    c2
    @104
    @113
    eqid
    @114
    eqid
    c2
    cn
    wcel
    @68
    2nn
    a1i
    @77
    @68
    @46
    c1
    @74
    @68
    1red
    #
    @43
    @48
    simpr
    ltled
    eftlub
    eqbrtrrd
    @72
    @89
    @71
    cmul
    c3
    @86
    c4
    @88
    cdiv
    df-3
    @88
    c2
    c2
    cmul
    co
    c4
    @87
    c2
    c2
    cmul
    fac2
    oveq1i
    2t2e4
    eqtr2i
    oveq12i
    oveq2i
    syl6breqr
    @68
    @73
    @71
    c1
    cmul
    co
    @71
    cle
    @68
    @72
    c1
    @71
    @82
    @68
    @85
    a1i
    @115
    @83
    @68
    @46
    @74
    sqge0d
    @72
    c1
    cle
    wbr
    @68
    @72
    c1
    @85
    1re
    @72
    c1
    clt
    wbr
    #
    c3
    c4
    c1
    cmul
    co
    #
    clt
    wbr
    #
    c3
    c4
    @117
    clt
    3lt4
    c4
    4cn
    mulid1i
    breqtrri
    @84
    @54
    c4
    cr
    wcel
    #
    cc0
    c4
    clt
    wbr
    #
    wa
    @116
    @118
    wb
    3re
    1re
    @119
    @120
    4re
    4pos
    pm3.2i
    c3
    c1
    c4
    ltdivmul
    mp3an
    mpbir
    ltleii
    a1i
    lemul2ad
    @68
    @71
    @68
    @46
    @68
    @46
    @74
    recnd
    #
    sqcld
    mulid1d
    breqtrd
    letrd
    @68
    @46
    @121
    sqvald
    breqtrd
    @68
    @60
    @46
    @46
    @81
    @74
    @68
    @46
    @74
    @68
    @18
    cc0
    @46
    clt
    wbr
    #
    @78
    @42
    @18
    @122
    wb
    @18
    @48
    @17
    absgt0
    ad2antrr
    mpbid
    elrpd
    lemul2d
    mpbird
    ad2ant2l
    @45
    @47
    @48
    simprl
    lelttrd
    eqbrtrd
    ex
    sylbid
    adantld
    sylan2b
    ralrimiva
    @30
    @40
    vy
    @35
    crp
    @21
    @35
    wceq
    #
    @29
    @39
    vw
    @5
    @123
    @23
    @38
    @28
    @123
    @22
    @37
    @18
    @21
    @35
    @20
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rgen
    @11
    @16
    @32
    wa
    wb
    wtru
    vx
    vy
    vw
    @5
    cc0
    c1
    @10
    @5
    cc
    @10
    wf
    wtru
    vz
    @5
    cc
    @9
    @10
    @62
    @6
    @5
    wcel
    #
    @8
    @6
    @124
    @7
    c1
    @124
    @6
    cc
    wcel
    @7
    cc
    wcel
    @6
    cc
    @4
    eldifi
    #
    @6
    efcl
    syl
    @124
    1cnd
    subcld
    @125
    @6
    cc
    cc0
    eldifsni
    divcld
    fmpti
    a1i
    wtru
    cc
    @4
    difssd
    wtru
    0cnd
    ellimc3
    trud
    mpbir2an
    @0
    @3
    @11
    wa
    wb
    wtru
    vz
    cc
    cc0
    c1
    cc
    @1
    ce
    @10
    @1
    @1
    cc
    crest
    co
    #
    @1
    @12
    @126
    @1
    wceq
    @14
    @1
    ctop
    cc
    @15
    restid
    ax-mp
    eqcomi
    @13
    vz
    @5
    @9
    @7
    cc0
    ce
    cfv
    #
    cmin
    co
    #
    @6
    cc0
    cmin
    co
    #
    cdiv
    co
    #
    @124
    @130
    @128
    @6
    cdiv
    co
    @9
    @124
    @129
    @6
    @128
    cdiv
    @124
    @6
    @125
    subid1d
    oveq2d
    @128
    @8
    @6
    cdiv
    @127
    c1
    @7
    cmin
    ef0
    oveq2i
    oveq1i
    syl6req
    mpteq2ia
    cc
    cc
    wss
    wtru
    cc
    ssid
    a1i
    #
    cc
    cc
    ce
    wf
    wtru
    eff
    a1i
    @131
    eldv
    trud
    mpbir2an
end
