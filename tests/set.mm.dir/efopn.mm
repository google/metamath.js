include "wcel.mm"
include "cv.mm"
include "ce.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cfv.mm"
include "cc.mm"
include "cpi.mm"
include "clt.mm"
include "wbr.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "toponss.mm"
include "mpan.mm"
include "sselda.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "w3a.mm"
include "pirp.mm"
include "cnfldtopn.mm"
include "mopni3.mm"
include "mpan2.mm"
include "mp3an1.mm"
include "imass2.mm"
include "wi.mm"
include "cdiv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cc0.mm"
include "crab.mm"
include "cin.mm"
include "wceq.mm"
include "crn.mm"
include "imassrn.mm"
include "wf.mm"
include "eff.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "cxr.mm"
include "rpxr.mm"
include "blssm.mm"
include "sylan2.mm"
include "ad2antrr.mm"
include "simp-4l.mm"
include "subcld.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "0cn.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "sylancl.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "wb.mm"
include "a1i.mm"
include "simpllr.mm"
include "adantr.mm"
include "rpxrd.mm"
include "elbl3.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "0cnd.mm"
include "mpbird.mm"
include "efsub.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "cmul.mm"
include "eqcom.mm"
include "simplr.mm"
include "efcl.mm"
include "syl.mm"
include "mp3an12.mm"
include "wne.mm"
include "efne0.mm"
include "divmuld.mm"
include "syl5bb.mm"
include "caddc.mm"
include "pncan2d.mm"
include "eqtr4d.mm"
include "addcld.mm"
include "efadd.mm"
include "eqeq2.mm"
include "sylbid.mm"
include "impbid.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelimab.mm"
include "sylancr.mm"
include "3bitr4d.mm"
include "rabbi2dva.mm"
include "syl5eqr.mm"
include "mptpreima.mm"
include "syl6eqr.mm"
include "ccn.mm"
include "ccncf.mm"
include "divccncf.mm"
include "cncfcn1.mm"
include "syl6eleq.mm"
include "efopnlem2.mm"
include "adantll.mm"
include "cnima.mm"
include "eqeltrd.mm"
include "blcntr.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "fdmi.mm"
include "syl6sseqr.mm"
include "funfvima2.mm"
include "mpd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "expr.mm"
include "syl5.mm"
include "expimpd.mm"
include "sylc.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "ralima.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "eltop2.mm"
include "sylibr.mm"

theorem efopn
  let cS: class S
  let cJ: class J
  let vr: setvar r
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  assume efopn.j: |- J = ( TopOpen ` CCfld )


  assert |- ( S e. J -> ( exp " S ) e. J )

  proof
    cS
    cJ
    wcel
    #
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    @2
    ce
    cS
    cima
    #
    wss
    #
    wa
    #
    vy
    cJ
    wrex
    #
    vz
    @4
    wral
    #
    @4
    cJ
    wcel
    #
    @0
    @8
    vx
    cv
    #
    ce
    cfv
    #
    @2
    wcel
    #
    @5
    wa
    #
    vy
    cJ
    wrex
    #
    vx
    cS
    wral
    #
    @0
    @14
    vx
    cS
    @0
    @10
    cS
    wcel
    #
    wa
    @10
    cc
    wcel
    #
    vr
    cv
    #
    cpi
    clt
    wbr
    #
    @10
    @18
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    cS
    wss
    #
    wa
    #
    vr
    crp
    wrex
    #
    @14
    @0
    cS
    cc
    @10
    cJ
    cc
    ctopon
    cfv
    wcel
    @0
    cS
    cc
    wss
    #
    cJ
    efopn.j
    cnfldtopon
    cS
    cJ
    cc
    toponss
    mpan
    #
    sselda
    @20
    cc
    cxmt
    cfv
    wcel
    #
    @0
    @16
    @25
    cnxmet
    @28
    @0
    @16
    w3a
    cpi
    crp
    wcel
    @25
    pirp
    vr
    cS
    @20
    @10
    cpi
    cJ
    cc
    cJ
    efopn.j
    cnfldtopn
    mopni3
    mpan2
    mp3an1
    @17
    @24
    @14
    vr
    crp
    @17
    @18
    crp
    wcel
    #
    wa
    #
    @19
    @23
    @14
    @23
    ce
    @22
    cima
    #
    @4
    wss
    #
    @30
    @19
    wa
    #
    @14
    @22
    cS
    ce
    imass2
    @33
    @31
    cJ
    wcel
    #
    @11
    @31
    wcel
    #
    @32
    @14
    wi
    @33
    @31
    vz
    cc
    @1
    @11
    cdiv
    co
    #
    cmpt
    #
    ccnv
    ce
    cc0
    @18
    @21
    co
    #
    cima
    #
    cima
    #
    cJ
    @33
    @31
    @36
    @39
    wcel
    #
    vz
    cc
    crab
    #
    @40
    @33
    @31
    cc
    @31
    cin
    #
    @42
    @31
    cc
    wss
    @43
    @31
    wceq
    @31
    ce
    crn
    #
    cc
    ce
    @22
    imassrn
    cc
    cc
    ce
    wf
    #
    @44
    cc
    wss
    eff
    cc
    cc
    ce
    frn
    ax-mp
    sstri
    @31
    cc
    sseqin2
    mpbi
    @33
    @41
    vz
    cc
    @31
    @33
    @1
    cc
    wcel
    #
    wa
    #
    @2
    ce
    cfv
    #
    @1
    wceq
    #
    vy
    @22
    wrex
    #
    vw
    cv
    #
    ce
    cfv
    #
    @36
    wceq
    #
    vw
    @38
    wrex
    #
    @1
    @31
    wcel
    #
    @41
    @47
    @50
    @54
    @47
    @49
    @54
    vy
    @22
    @47
    @2
    @22
    wcel
    #
    wa
    #
    @52
    @48
    @11
    cdiv
    co
    #
    wceq
    #
    vw
    @38
    wrex
    #
    @49
    @54
    @57
    @2
    @10
    cmin
    co
    #
    @38
    wcel
    #
    @61
    ce
    cfv
    #
    @58
    wceq
    #
    @60
    @57
    @62
    @61
    cc0
    @20
    co
    #
    @18
    clt
    wbr
    #
    @57
    @65
    @2
    @10
    @20
    co
    #
    @18
    clt
    @57
    @61
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @61
    cabs
    cfv
    #
    @65
    @67
    @57
    @68
    @61
    cabs
    @57
    @61
    @57
    @2
    @10
    @47
    @22
    cc
    @2
    @30
    @22
    cc
    wss
    #
    @19
    @46
    @29
    @17
    @18
    cxr
    wcel
    #
    @71
    @18
    rpxr
    @28
    @17
    @72
    @71
    cnxmet
    @20
    @10
    @18
    cc
    blssm
    mp3an1
    sylan2
    #
    ad2antrr
    #
    sselda
    #
    @17
    @29
    @19
    @46
    @56
    simp-4l
    #
    subcld
    #
    subid1d
    fveq2d
    @57
    @61
    cc
    wcel
    #
    cc0
    cc
    wcel
    #
    @65
    @69
    wceq
    @77
    0cn
    @61
    cc0
    @20
    @20
    eqid
    #
    cnmetdval
    sylancl
    @57
    @2
    cc
    wcel
    #
    @17
    @67
    @70
    wceq
    @75
    @76
    @2
    @10
    @20
    @80
    cnmetdval
    syl2anc
    3eqtr4d
    @57
    @56
    @67
    @18
    clt
    wbr
    #
    @47
    @56
    simpr
    @57
    @28
    @72
    @17
    @81
    @56
    @82
    wb
    @28
    @57
    cnxmet
    a1i
    #
    @57
    @18
    @47
    @29
    @56
    @17
    @29
    @19
    @46
    simpllr
    #
    adantr
    rpxrd
    #
    @76
    @75
    @2
    @20
    @10
    @18
    cc
    elbl3
    syl22anc
    mpbid
    eqbrtrd
    @57
    @28
    @72
    @79
    @78
    @62
    @66
    wb
    @83
    @85
    @57
    0cnd
    @77
    @61
    @20
    cc0
    @18
    cc
    elbl3
    syl22anc
    mpbird
    @57
    @81
    @17
    @64
    @75
    @76
    @2
    @10
    efsub
    syl2anc
    @59
    @64
    vw
    @61
    @38
    @51
    @61
    wceq
    @52
    @63
    @58
    @51
    @61
    ce
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @49
    @59
    @53
    vw
    @38
    @49
    @58
    @36
    @52
    @48
    @1
    @11
    cdiv
    oveq1
    eqeq2d
    rexbidv
    syl5ibcom
    rexlimdva
    @47
    @53
    @50
    vw
    @38
    @47
    @51
    @38
    wcel
    #
    wa
    #
    @53
    @11
    @52
    cmul
    co
    #
    @1
    wceq
    #
    @50
    @53
    @36
    @52
    wceq
    @87
    @89
    @52
    @36
    eqcom
    @87
    @1
    @11
    @52
    @33
    @46
    @86
    simplr
    @87
    @17
    @11
    cc
    wcel
    #
    @17
    @29
    @19
    @46
    @86
    simp-4l
    #
    @10
    efcl
    #
    syl
    @87
    @51
    cc
    wcel
    #
    @52
    cc
    wcel
    @47
    @38
    cc
    @51
    @47
    @72
    @38
    cc
    wss
    #
    @47
    @18
    @84
    rpxrd
    @28
    @79
    @72
    @94
    cnxmet
    0cn
    @20
    cc0
    @18
    cc
    blssm
    mp3an12
    syl
    #
    sselda
    #
    @51
    efcl
    syl
    @87
    @17
    @11
    cc0
    wne
    #
    @91
    @10
    efne0
    #
    syl
    divmuld
    syl5bb
    @87
    @48
    @88
    wceq
    #
    vy
    @22
    wrex
    #
    @89
    @50
    @87
    @10
    @51
    caddc
    co
    #
    @22
    wcel
    #
    @101
    ce
    cfv
    #
    @88
    wceq
    #
    @100
    @87
    @102
    @101
    @10
    @20
    co
    #
    @18
    clt
    wbr
    #
    @87
    @105
    @51
    cc0
    @20
    co
    #
    @18
    clt
    @87
    @101
    @10
    cmin
    co
    #
    cabs
    cfv
    #
    @51
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @105
    @107
    @87
    @108
    @110
    cabs
    @87
    @108
    @51
    @110
    @87
    @10
    @51
    @91
    @96
    pncan2d
    @87
    @51
    @96
    subid1d
    eqtr4d
    fveq2d
    @87
    @101
    cc
    wcel
    #
    @17
    @105
    @109
    wceq
    @87
    @10
    @51
    @91
    @96
    addcld
    #
    @91
    @101
    @10
    @20
    @80
    cnmetdval
    syl2anc
    @87
    @93
    @79
    @107
    @111
    wceq
    @96
    0cn
    @51
    cc0
    @20
    @80
    cnmetdval
    sylancl
    3eqtr4d
    @87
    @86
    @107
    @18
    clt
    wbr
    #
    @47
    @86
    simpr
    @87
    @28
    @72
    @79
    @93
    @86
    @114
    wb
    @28
    @87
    cnxmet
    a1i
    #
    @87
    @18
    @47
    @29
    @86
    @84
    adantr
    rpxrd
    #
    @87
    0cnd
    @96
    @51
    @20
    cc0
    @18
    cc
    elbl3
    syl22anc
    mpbid
    eqbrtrd
    @87
    @28
    @72
    @17
    @112
    @102
    @106
    wb
    @115
    @116
    @91
    @113
    @101
    @20
    @10
    @18
    cc
    elbl3
    syl22anc
    mpbird
    @87
    @17
    @93
    @104
    @91
    @96
    @10
    @51
    efadd
    syl2anc
    @99
    @104
    vy
    @101
    @22
    @2
    @101
    wceq
    @48
    @103
    @88
    @2
    @101
    ce
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @89
    @99
    @49
    vy
    @22
    @88
    @1
    @48
    eqeq2
    rexbidv
    syl5ibcom
    sylbid
    rexlimdva
    impbid
    @47
    ce
    cc
    wfn
    #
    @71
    @55
    @50
    wb
    @45
    @117
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    #
    @74
    vy
    cc
    @22
    @1
    ce
    fvelimab
    sylancr
    @47
    @117
    @94
    @41
    @54
    wb
    @118
    @95
    vw
    cc
    @38
    @36
    ce
    fvelimab
    sylancr
    3bitr4d
    rabbi2dva
    syl5eqr
    vz
    cc
    @36
    @39
    @37
    @37
    eqid
    #
    mptpreima
    syl6eqr
    @33
    @37
    cJ
    cJ
    ccn
    co
    #
    wcel
    @39
    cJ
    wcel
    #
    @40
    cJ
    wcel
    @33
    @37
    cc
    cc
    ccncf
    co
    #
    @120
    @33
    @90
    @97
    @37
    @122
    wcel
    @17
    @90
    @29
    @19
    @92
    ad2antrr
    @17
    @97
    @29
    @19
    @98
    ad2antrr
    vz
    @11
    @37
    @119
    divccncf
    syl2anc
    cJ
    efopn.j
    cncfcn1
    syl6eleq
    @29
    @19
    @121
    @17
    @18
    cJ
    efopn.j
    efopnlem2
    adantll
    @39
    @37
    cJ
    cJ
    cnima
    syl2anc
    eqeltrd
    @30
    @35
    @19
    @30
    @10
    @22
    wcel
    #
    @35
    @28
    @17
    @29
    @123
    cnxmet
    @20
    @10
    @18
    cc
    blcntr
    mp3an1
    @30
    ce
    wfun
    #
    @22
    ce
    cdm
    #
    wss
    @123
    @35
    wi
    @45
    @124
    eff
    cc
    cc
    ce
    ffun
    ax-mp
    @30
    @22
    cc
    @125
    @73
    cc
    cc
    ce
    eff
    fdmi
    syl6sseqr
    @22
    @10
    ce
    funfvima2
    sylancr
    mpd
    adantr
    @34
    @35
    @32
    @14
    @13
    @35
    @32
    wa
    vy
    @31
    cJ
    @2
    @31
    wceq
    @12
    @35
    @5
    @32
    @2
    @31
    @11
    eleq2
    @2
    @31
    @4
    sseq1
    anbi12d
    rspcev
    expr
    syl2anc
    syl5
    expimpd
    rexlimdva
    sylc
    ralrimiva
    @0
    @117
    @26
    @8
    @15
    wb
    @118
    @27
    @7
    @14
    vz
    vx
    cc
    cS
    ce
    @1
    @11
    wceq
    #
    @6
    @13
    vy
    cJ
    @126
    @3
    @12
    @5
    @1
    @11
    @2
    eleq1
    anbi1d
    rexbidv
    ralima
    sylancr
    mpbird
    cJ
    ctop
    wcel
    @9
    @8
    wb
    cJ
    efopn.j
    cnfldtop
    vz
    vy
    @4
    cJ
    eltop2
    ax-mp
    sylibr
end
