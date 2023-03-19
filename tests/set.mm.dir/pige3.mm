include "c1.mm"
include "c3.mm"
include "cmul.mm"
include "co.mm"
include "cpi.mm"
include "cle.mm"
include "3cn.mm"
include "mulid2i.mm"
include "wbr.mm"
include "cdiv.mm"
include "ci.mm"
include "cneg.mm"
include "ce.mm"
include "cfv.mm"
include "cabs.mm"
include "cc0.mm"
include "cicc.mm"
include "cv.mm"
include "cmpt.mm"
include "cmin.mm"
include "wtru.mm"
include "wcel.mm"
include "wa.mm"
include "tru.mm"
include "cxr.mm"
include "0xr.mm"
include "crp.mm"
include "pirp.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "rpdivcl.mm"
include "mp2an.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "rpge0.mm"
include "lbicc2.mm"
include "mp3an.mm"
include "ubicc2.mm"
include "pm3.2i.mm"
include "cr.mm"
include "0re.mm"
include "a1i.mm"
include "pire.mm"
include "3ne0.mm"
include "redivcli.mm"
include "cc.mm"
include "ccncf.mm"
include "efcn.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "iccssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "resmpt.mm"
include "mp1i.mm"
include "wf.mm"
include "cdv.mm"
include "cdm.mm"
include "ssid.mm"
include "ax-icn.mm"
include "simpr.mm"
include "mulcl.mm"
include "sylancr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "ax-1cn.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1i.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "dmeqd.mm"
include "elexi.mm"
include "dmmpti.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "rescncf.mm"
include "mpsyl.mm"
include "eqeltrrd.mm"
include "cncfmpt1f.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "reelprrecn.mm"
include "recn.mm"
include "efcl.mm"
include "syl.mm"
include "sylan2.mm"
include "sylancl.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "toponmax.mm"
include "cin.mm"
include "df-ss.mm"
include "sylib.mm"
include "adantl.mm"
include "dvef.mm"
include "eff.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "3eqtr3a.mm"
include "fveq2.mm"
include "dvmptco.mm"
include "dvmptres3.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptres2.mm"
include "ovex.mm"
include "1re.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "fvmpt3i.mm"
include "sylan9eq.mm"
include "ioossre.mm"
include "sselda.mm"
include "recnd.mm"
include "absmul.mm"
include "absefi.mm"
include "absi.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "dvlip.mm"
include "it0e0.mm"
include "ef0.mm"
include "fvex.mm"
include "oveq12i.mm"
include "recni.mm"
include "mulcli.mm"
include "negicn.mm"
include "caddc.mm"
include "c2.mm"
include "ccos.mm"
include "cosval.mm"
include "csin.mm"
include "csqrt.mm"
include "sincos3rdpi.mm"
include "simpri.mm"
include "eqtr3i.mm"
include "addcli.mm"
include "2cn.mm"
include "2ne0.mm"
include "div11i.mm"
include "mpbi.mm"
include "subaddrii.mm"
include "mulneg12.mm"
include "fveq2i.mm"
include "3eqtri.mm"
include "absnegi.mm"
include "df-neg.mm"
include "rprege0.mm"
include "absid.mm"
include "mp2b.mm"
include "oveq2i.mm"
include "3brtr3i.mm"
include "renegcli.mm"
include "clt.mm"
include "wb.mm"
include "lemuldiv.mm"
include "mpbir.mm"
include "eqbrtrri.mm"

theorem pige3
  let vx: setvar x
  let vy: setvar y


  assert |- 3 <_ _pi

  proof
    c1
    c3
    cmul
    co
    #
    c3
    cpi
    cle
    c3
    3cn
    mulid2i
    @0
    cpi
    cle
    wbr
    #
    c1
    cpi
    c3
    cdiv
    co
    #
    cle
    wbr
    #
    ci
    @2
    cneg
    #
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    c1
    @2
    cmul
    co
    #
    c1
    @2
    cle
    cc0
    vx
    cc0
    @2
    cicc
    co
    #
    ci
    vx
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cmpt
    #
    cfv
    #
    @2
    @13
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    cc0
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @7
    @8
    cle
    wtru
    cc0
    @9
    wcel
    #
    @2
    @9
    wcel
    #
    wa
    @17
    @20
    cle
    wbr
    tru
    @21
    @22
    cc0
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @21
    0xr
    @2
    crp
    wcel
    #
    @24
    cpi
    crp
    wcel
    c3
    crp
    wcel
    @26
    pirp
    c3
    3re
    3pos
    elrpii
    cpi
    c3
    rpdivcl
    mp2an
    #
    @2
    rpxr
    ax-mp
    #
    @26
    @25
    @27
    @2
    rpge0
    ax-mp
    #
    cc0
    @2
    lbicc2
    mp3an
    #
    @23
    @24
    @25
    @22
    0xr
    @28
    @29
    cc0
    @2
    ubicc2
    mp3an
    #
    pm3.2i
    wtru
    vy
    cc0
    @2
    @13
    c1
    cc0
    @2
    cc0
    cr
    wcel
    #
    wtru
    0re
    a1i
    @2
    cr
    wcel
    #
    wtru
    cpi
    c3
    pire
    3re
    3ne0
    redivcli
    #
    a1i
    #
    wtru
    vx
    @11
    ce
    @9
    ce
    cc
    cc
    ccncf
    co
    #
    wcel
    wtru
    efcn
    a1i
    wtru
    vx
    cc
    @11
    cmpt
    #
    @9
    cres
    #
    vx
    @9
    @11
    cmpt
    #
    @9
    cc
    ccncf
    co
    #
    @9
    cc
    wss
    #
    @38
    @39
    wceq
    wtru
    @9
    cr
    cc
    @32
    @33
    @9
    cr
    wss
    #
    0re
    @34
    cc0
    @2
    iccssre
    mp2an
    #
    ax-resscn
    sstri
    #
    vx
    cc
    @9
    @11
    resmpt
    mp1i
    @41
    wtru
    @37
    @36
    wcel
    #
    @38
    @40
    wcel
    @44
    wtru
    cc
    cc
    wss
    #
    cc
    cc
    @37
    wf
    @46
    cc
    @37
    cdv
    co
    #
    cdm
    #
    cc
    wceq
    @45
    @46
    wtru
    cc
    ssid
    a1i
    #
    wtru
    vx
    cc
    @11
    cc
    @37
    wtru
    @10
    cc
    wcel
    #
    wa
    #
    ci
    cc
    wcel
    #
    @50
    @11
    cc
    wcel
    #
    ax-icn
    wtru
    @50
    simpr
    #
    ci
    @10
    mulcl
    sylancr
    #
    @37
    eqid
    fmptd
    @49
    wtru
    @48
    vx
    cc
    ci
    cmpt
    #
    cdm
    cc
    wtru
    @47
    @56
    wtru
    @47
    vx
    cc
    ci
    c1
    cmul
    co
    #
    cmpt
    @56
    wtru
    vx
    @10
    c1
    ci
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    #
    wcel
    wtru
    cnelprrecn
    a1i
    #
    @54
    c1
    cc
    wcel
    @51
    ax-1cn
    a1i
    wtru
    vx
    cc
    @59
    dvmptid
    @52
    wtru
    ax-icn
    a1i
    dvmptcmul
    vx
    cc
    @57
    ci
    ci
    ax-icn
    mulid1i
    mpteq2i
    syl6eq
    #
    dmeqd
    vx
    cc
    ci
    @56
    ci
    cc
    ax-icn
    elexi
    @56
    eqid
    dmmpti
    syl6eq
    cc
    cc
    @37
    dvcn
    syl31anc
    cc
    cc
    @9
    @37
    rescncf
    mpsyl
    eqeltrrd
    cncfmpt1f
    wtru
    cr
    @13
    cdv
    co
    #
    cdm
    vx
    cc0
    @2
    cioo
    co
    #
    @12
    ci
    cmul
    co
    #
    cmpt
    #
    cdm
    @62
    wtru
    @61
    @64
    wtru
    vx
    @12
    @63
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    cc
    cr
    @62
    @9
    cr
    @58
    wcel
    wtru
    reelprrecn
    a1i
    #
    @10
    cr
    wcel
    #
    wtru
    @50
    @12
    cc
    wcel
    #
    @10
    recn
    #
    @51
    @53
    @69
    @55
    @11
    efcl
    syl
    #
    sylan2
    @68
    wtru
    @50
    @63
    cc
    wcel
    #
    @70
    @51
    @69
    @52
    @72
    @71
    ax-icn
    @12
    ci
    mulcl
    sylancl
    #
    sylan2
    wtru
    vx
    @12
    @63
    cr
    @66
    cc
    cc
    cr
    @66
    eqid
    #
    @67
    @66
    cc
    ctopon
    cfv
    wcel
    cc
    @66
    wcel
    wtru
    @66
    @74
    cnfldtopon
    cc
    @66
    toponmax
    mp1i
    wtru
    cr
    cc
    wss
    #
    cr
    cc
    cin
    cr
    wceq
    @75
    wtru
    ax-resscn
    a1i
    cr
    cc
    df-ss
    sylib
    @71
    @73
    wtru
    vx
    vy
    @11
    ci
    vy
    cv
    #
    ce
    cfv
    #
    @77
    cc
    cc
    @12
    @12
    cc
    cc
    cc
    cc
    @59
    @59
    @55
    @52
    @51
    ax-icn
    a1i
    @76
    cc
    wcel
    #
    @77
    cc
    wcel
    wtru
    @76
    efcl
    adantl
    #
    @79
    @60
    wtru
    cc
    ce
    cdv
    co
    ce
    cc
    vy
    cc
    @77
    cmpt
    #
    cdv
    co
    @80
    dvef
    wtru
    ce
    @80
    cc
    cdv
    wtru
    vy
    cc
    cc
    ce
    cc
    cc
    ce
    wf
    wtru
    eff
    a1i
    feqmptd
    #
    oveq2d
    @81
    3eqtr3a
    @76
    @11
    ce
    fveq2
    #
    @82
    dvmptco
    dvmptres3
    @42
    wtru
    @43
    a1i
    @66
    @74
    tgioo2
    @74
    wtru
    @32
    @33
    @9
    @65
    cnt
    cfv
    cfv
    @62
    wceq
    0re
    @35
    cc0
    @2
    iccntr
    sylancr
    dvmptres2
    #
    dmeqd
    vx
    @62
    @63
    @64
    @12
    ci
    cmul
    ovex
    #
    @64
    eqid
    #
    dmmpti
    syl6eq
    c1
    cr
    wcel
    #
    wtru
    1re
    a1i
    wtru
    @76
    @62
    wcel
    #
    wa
    #
    @76
    @61
    cfv
    #
    cabs
    cfv
    #
    c1
    c1
    cle
    @88
    @90
    ci
    @76
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cmul
    co
    #
    cabs
    cfv
    #
    @92
    cabs
    cfv
    #
    ci
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    @88
    @89
    @93
    cabs
    wtru
    @87
    @89
    @76
    @64
    cfv
    @93
    wtru
    @76
    @61
    @64
    @83
    fveq1d
    vx
    @76
    @63
    @93
    @62
    @64
    @10
    @76
    wceq
    #
    @12
    @92
    ci
    cmul
    @98
    @11
    @91
    ce
    @10
    @76
    ci
    cmul
    oveq2
    fveq2d
    oveq1d
    @85
    @84
    fvmpt3i
    sylan9eq
    fveq2d
    @88
    @92
    cc
    wcel
    #
    @52
    @94
    @97
    wceq
    @88
    @91
    cc
    wcel
    #
    @99
    @88
    @52
    @78
    @100
    ax-icn
    @88
    @76
    wtru
    @62
    cr
    @76
    @62
    cr
    wss
    wtru
    cc0
    @2
    ioossre
    a1i
    sselda
    #
    recnd
    ci
    @76
    mulcl
    sylancr
    @91
    efcl
    syl
    ax-icn
    @92
    ci
    absmul
    sylancl
    @88
    @97
    c1
    c1
    cmul
    co
    c1
    @88
    @95
    c1
    @96
    c1
    cmul
    @88
    @76
    cr
    wcel
    @95
    c1
    wceq
    @101
    @76
    absefi
    syl
    @96
    c1
    wceq
    @88
    absi
    a1i
    oveq12d
    c1
    ax-1cn
    mulid1i
    syl6eq
    3eqtrd
    1le1
    syl6eqbr
    dvlip
    mp2an
    @16
    @6
    cabs
    @16
    c1
    ci
    @2
    cmul
    co
    #
    ce
    cfv
    #
    cmin
    co
    ci
    cneg
    #
    @2
    cmul
    co
    #
    ce
    cfv
    #
    @6
    @14
    c1
    @15
    @103
    cmin
    @21
    @14
    c1
    wceq
    @30
    vx
    cc0
    @12
    c1
    @9
    @13
    @10
    cc0
    wceq
    #
    @12
    cc0
    ce
    cfv
    c1
    @107
    @11
    cc0
    ce
    @107
    @11
    ci
    cc0
    cmul
    co
    cc0
    @10
    cc0
    ci
    cmul
    oveq2
    it0e0
    syl6eq
    fveq2d
    ef0
    syl6eq
    @13
    eqid
    #
    @11
    ce
    fvex
    #
    fvmpt3i
    ax-mp
    @22
    @15
    @103
    wceq
    @31
    vx
    @2
    @12
    @103
    @9
    @13
    @10
    @2
    wceq
    @11
    @102
    ce
    @10
    @2
    ci
    cmul
    oveq2
    fveq2d
    @108
    @109
    fvmpt3i
    ax-mp
    oveq12i
    c1
    @103
    @106
    ax-1cn
    @102
    cc
    wcel
    @103
    cc
    wcel
    ci
    @2
    ax-icn
    @2
    @34
    recni
    #
    mulcli
    @102
    efcl
    ax-mp
    #
    @105
    cc
    wcel
    @106
    cc
    wcel
    @104
    @2
    negicn
    @110
    mulcli
    @105
    efcl
    ax-mp
    #
    @103
    @106
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    wceq
    @113
    c1
    wceq
    @2
    ccos
    cfv
    #
    @114
    @115
    @2
    cc
    wcel
    #
    @116
    @114
    wceq
    @110
    @2
    cosval
    ax-mp
    @2
    csin
    cfv
    c3
    csqrt
    cfv
    c2
    cdiv
    co
    wceq
    @116
    @115
    wceq
    sincos3rdpi
    simpri
    eqtr3i
    @113
    c1
    c2
    @103
    @106
    @111
    @112
    addcli
    ax-1cn
    2cn
    2ne0
    div11i
    mpbi
    subaddrii
    @105
    @5
    ce
    @52
    @117
    @105
    @5
    wceq
    ax-icn
    @110
    ci
    @2
    mulneg12
    mp2an
    fveq2i
    3eqtri
    fveq2i
    @19
    @2
    c1
    cmul
    @2
    cabs
    cfv
    #
    @19
    @2
    @4
    cabs
    cfv
    @118
    @19
    @2
    @110
    absnegi
    @4
    @18
    cabs
    @2
    df-neg
    fveq2i
    eqtr3i
    @26
    @33
    @25
    wa
    @118
    @2
    wceq
    @27
    @2
    rprege0
    @2
    absid
    mp2b
    eqtr3i
    oveq2i
    3brtr3i
    @4
    cr
    wcel
    @7
    c1
    wceq
    @2
    @34
    renegcli
    @4
    absefi
    ax-mp
    @2
    @110
    mulid2i
    3brtr3i
    @86
    cpi
    cr
    wcel
    c3
    cr
    wcel
    #
    cc0
    c3
    clt
    wbr
    #
    wa
    @1
    @3
    wb
    1re
    pire
    @119
    @120
    3re
    3pos
    pm3.2i
    c1
    cpi
    c3
    lemuldiv
    mp3an
    mpbir
    eqbrtrri
end
