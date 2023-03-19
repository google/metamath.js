include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ctotbnd.mm"
include "cv.mm"
include "cbl.mm"
include "co.mm"
include "ciun.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "wceq.mm"
include "wb.mm"
include "cxp.mm"
include "cres.mm"
include "metres2.mm"
include "syl5eqel.mm"
include "istotbnd3.mm"
include "baib.mm"
include "syl.mm"
include "simpllr.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssrin.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "wel.mm"
include "cxmt.mm"
include "cxr.mm"
include "metxmet.mm"
include "ad4antr.mm"
include "elfpw.mm"
include "simplbi.mm"
include "adantl.mm"
include "sselda.mm"
include "simp-4r.mm"
include "sseqin2.mm"
include "eleqtrrd.mm"
include "rpxrd.mm"
include "blres.mm"
include "syl3anc.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "ralrimiva.mm"
include "ss2iun.mm"
include "adantrr.mm"
include "eqsstr3d.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "ralimdva.mm"
include "sylbid.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "simpr.mm"
include "rphalfcld.mm"
include "oveq2.mm"
include "iuneq2d.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wf.mm"
include "wex.mm"
include "simprbi.mm"
include "ad2antrl.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "weq.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "incom.mm"
include "syl6eq.mm"
include "dfin5.mm"
include "neeq1d.mm"
include "rabn0.mm"
include "syl6bb.mm"
include "elrab.mm"
include "rgen.mm"
include "eleq1.mm"
include "ac6sfi.mm"
include "cdm.mm"
include "ccnv.mm"
include "cima.mm"
include "w3a.mm"
include "fdm.mm"
include "feq2d.mm"
include "mpbird.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "baibd.mm"
include "ralbidva.mm"
include "id.mm"
include "imaeq2d.mm"
include "eleq12d.mm"
include "ralrab2.mm"
include "3jca.mm"
include "crn.mm"
include "simpr2.mm"
include "frn.mm"
include "adantr.mm"
include "simpr1.mm"
include "syl2anc.mm"
include "fnfi.mm"
include "rnfi.mm"
include "sylanbrc.mm"
include "cbviunv.mm"
include "rpxr.mm"
include "ad4antlr.mm"
include "blssm.mm"
include "iunss.mm"
include "sylibr.mm"
include "iunin1.mm"
include "simplrr.mm"
include "syl6sseq.mm"
include "syl5eq.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "simpr3.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "cr.mm"
include "ad5antr.mm"
include "cnvimass.mm"
include "sstrd.mm"
include "syl5ss.mm"
include "rpred.mm"
include "simplbda.mm"
include "blhalf.mm"
include "syl22anc.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "simp-5r.mm"
include "sseqtr4d.mm"
include "fnfvelrn.mm"
include "ssiun2s.mm"
include "adantlr.mm"
include "syld.mm"
include "pm2.61dne.mm"
include "eqssd.mm"
include "iuneq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "exlimdv.mm"
include "mpd.mm"
include "rexlimdvaa.mm"
include "ralrimdva.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem sstotbnd2
  let vx: setvar x
  let vv: setvar v
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume sstotbnd.2: |- N = ( M |` ( Y X. Y ) )

  disjoint d v
  disjoint d x
  disjoint M d
  disjoint v x
  disjoint M v
  disjoint M x
  disjoint X d
  disjoint X v
  disjoint X x
  disjoint N d
  disjoint N v
  disjoint N x
  disjoint Y d
  disjoint Y v
  disjoint Y x
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint M b
  disjoint c d
  disjoint c f
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint M c
  disjoint d f
  disjoint d u
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint M f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint M u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint X b
  disjoint X c
  disjoint X f
  disjoint X u
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint N c
  disjoint N f
  disjoint N u
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint Y b
  disjoint Y c
  disjoint Y f
  disjoint Y u
  disjoint Y w
  disjoint Y y
  disjoint Y z
  assert |- ( ( M e. ( Met ` X ) /\ Y C_ X ) -> ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. ( ~P X i^i Fin ) Y C_ U_ x e. v ( x ( ball ` M ) d ) ) )

  proof
    cM
    cX
    cme
    cfv
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cN
    cY
    ctotbnd
    cfv
    wcel
    #
    cY
    vx
    vv
    cv
    #
    vx
    cv
    #
    vd
    cv
    #
    cM
    cbl
    cfv
    #
    co
    #
    ciun
    #
    wss
    #
    vv
    cX
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vd
    crp
    wral
    #
    @2
    @3
    vx
    @4
    @5
    @6
    cN
    cbl
    cfv
    #
    co
    #
    ciun
    #
    cY
    wceq
    #
    vv
    cY
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vd
    crp
    wral
    #
    @14
    @2
    cN
    cY
    cme
    cfv
    #
    wcel
    #
    @3
    @22
    wb
    @2
    cN
    cM
    cY
    cY
    cxp
    cres
    @23
    sstotbnd.2
    cM
    cY
    cX
    metres2
    syl5eqel
    #
    @3
    @24
    @22
    vx
    vv
    cN
    cY
    vd
    istotbnd3
    baib
    syl
    @2
    @21
    @13
    vd
    crp
    @2
    @6
    crp
    wcel
    #
    wa
    #
    @18
    @10
    vv
    @20
    @12
    @27
    @4
    @20
    wcel
    #
    @18
    wa
    #
    @4
    @12
    wcel
    #
    @10
    wa
    @27
    @29
    wa
    #
    @30
    @10
    @31
    @20
    @12
    @4
    @31
    @19
    @11
    wss
    #
    @20
    @12
    wss
    @31
    @1
    @32
    @0
    @1
    @26
    @29
    simpllr
    cY
    cX
    sspwb
    sylib
    @19
    @11
    cfn
    ssrin
    syl
    @27
    @28
    @18
    simprl
    sseldd
    @31
    cY
    @17
    @9
    @27
    @28
    @18
    simprr
    @27
    @28
    @17
    @9
    wss
    #
    @18
    @27
    @28
    wa
    #
    @16
    @8
    wss
    #
    vx
    @4
    wral
    @33
    @34
    @35
    vx
    @4
    @34
    vx
    vv
    wel
    #
    wa
    #
    @16
    @8
    cY
    cin
    #
    @8
    @37
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @5
    cX
    cY
    cin
    #
    wcel
    @6
    cxr
    wcel
    @16
    @38
    wceq
    @0
    @39
    @1
    @26
    @28
    @36
    cM
    cX
    metxmet
    #
    ad4antr
    @37
    @5
    cY
    @40
    @34
    @4
    cY
    @5
    @28
    @4
    cY
    wss
    #
    @27
    @28
    @42
    @4
    cfn
    wcel
    #
    @4
    cY
    elfpw
    simplbi
    adantl
    sselda
    @37
    @1
    @40
    cY
    wceq
    #
    @0
    @1
    @26
    @28
    @36
    simp-4r
    cY
    cX
    sseqin2
    #
    sylib
    eleqtrrd
    @37
    @6
    @2
    @26
    @28
    @36
    simpllr
    rpxrd
    cN
    cM
    @5
    @6
    cX
    cY
    sstotbnd.2
    blres
    syl3anc
    @8
    cY
    inss1
    syl6eqss
    ralrimiva
    vx
    @4
    @16
    @8
    ss2iun
    syl
    adantrr
    eqsstr3d
    jca
    ex
    reximdv2
    ralimdva
    sylbid
    @2
    @14
    vx
    vw
    cv
    #
    @5
    vc
    cv
    #
    @15
    co
    #
    ciun
    #
    cY
    wceq
    #
    vw
    @20
    wrex
    #
    vc
    crp
    wral
    #
    @3
    @2
    @14
    @51
    vc
    crp
    @2
    @47
    crp
    wcel
    #
    wa
    #
    @14
    cY
    vx
    @4
    @5
    @47
    c2
    cdiv
    co
    #
    @7
    co
    #
    ciun
    #
    wss
    #
    vv
    @12
    wrex
    #
    @51
    @54
    @55
    crp
    wcel
    @14
    @59
    wi
    @54
    @47
    @2
    @53
    simpr
    rphalfcld
    @13
    @59
    vd
    @55
    crp
    @6
    @55
    wceq
    #
    @10
    @58
    vv
    @12
    @60
    @9
    @57
    cY
    @60
    vx
    @4
    @8
    @56
    @6
    @55
    @5
    @7
    oveq2
    iuneq2d
    sseq2d
    rexbidv
    rspcv
    syl
    @54
    @58
    @51
    vv
    @12
    @54
    @30
    @58
    wa
    #
    wa
    #
    @56
    cY
    cin
    #
    c0
    wne
    #
    vx
    @4
    crab
    #
    cY
    vf
    cv
    #
    wf
    #
    vy
    cv
    #
    @66
    cfv
    #
    @68
    @55
    @7
    co
    #
    wcel
    #
    vy
    @65
    wral
    #
    wa
    #
    vf
    wex
    #
    @51
    @62
    @65
    cfn
    wcel
    #
    vz
    cv
    #
    @70
    wcel
    #
    vz
    cY
    wrex
    #
    vy
    @65
    wral
    @74
    @62
    @43
    @65
    @4
    wss
    @75
    @30
    @43
    @54
    @58
    @30
    @4
    cX
    wss
    #
    @43
    @4
    cX
    elfpw
    #
    simprbi
    ad2antrl
    #
    @64
    vx
    @4
    ssrab2
    #
    @4
    @65
    ssfi
    sylancl
    @78
    vy
    @65
    @68
    @65
    wcel
    #
    vy
    vv
    wel
    #
    @78
    @64
    @78
    vx
    @68
    @4
    vx
    vy
    weq
    #
    @64
    @77
    vz
    cY
    crab
    #
    c0
    wne
    @78
    @85
    @63
    @86
    c0
    @85
    @63
    cY
    @70
    cin
    #
    @86
    @85
    @63
    @70
    cY
    cin
    #
    @87
    @85
    @56
    @70
    cY
    @5
    @68
    @55
    @7
    oveq1
    #
    ineq1d
    #
    @70
    cY
    incom
    syl6eq
    vz
    cY
    @70
    dfin5
    syl6eq
    neeq1d
    @77
    vz
    cY
    rabn0
    syl6bb
    elrab
    simprbi
    rgen
    @77
    @71
    vy
    vz
    @65
    cY
    vf
    @76
    @69
    @70
    eleq1
    ac6sfi
    sylancl
    @62
    @73
    @51
    vf
    @62
    @73
    @66
    cdm
    #
    @4
    wss
    #
    @91
    cY
    @66
    wf
    #
    @64
    @5
    @66
    ccnv
    #
    @56
    cima
    #
    wcel
    #
    wi
    #
    vx
    @4
    wral
    #
    w3a
    #
    @51
    @62
    @43
    @73
    @99
    wi
    @81
    @43
    @73
    @99
    @43
    @73
    wa
    #
    @92
    @93
    @98
    @100
    @91
    @65
    @4
    @67
    @91
    @65
    wceq
    @43
    @72
    @65
    cY
    @66
    fdm
    ad2antrl
    #
    @82
    syl6eqss
    @100
    @93
    @67
    @43
    @67
    @72
    simprl
    @100
    @91
    @65
    cY
    @66
    @101
    feq2d
    mpbird
    @100
    @68
    @94
    @70
    cima
    #
    wcel
    #
    vy
    @65
    wral
    #
    @98
    @100
    @104
    @72
    @43
    @67
    @72
    simprr
    @67
    @104
    @72
    wb
    @43
    @72
    @67
    @103
    @71
    vy
    @65
    @67
    @103
    @83
    @71
    @67
    @66
    @65
    wfn
    @103
    @83
    @71
    wa
    wb
    @65
    cY
    @66
    ffn
    @65
    @68
    @70
    @66
    elpreima
    syl
    baibd
    ralbidva
    ad2antrl
    mpbird
    @64
    @103
    @96
    vy
    vx
    @4
    vy
    vx
    weq
    #
    @68
    @5
    @102
    @95
    @105
    id
    @105
    @70
    @56
    @94
    @68
    @5
    @55
    @7
    oveq1
    imaeq2d
    eleq12d
    ralrab2
    sylib
    3jca
    ex
    syl
    @62
    @99
    @51
    @62
    @99
    wa
    #
    @66
    crn
    #
    @20
    wcel
    #
    vx
    @107
    @48
    ciun
    #
    cY
    wceq
    #
    @51
    @106
    @107
    cY
    wss
    #
    @107
    cfn
    wcel
    #
    @108
    @106
    @93
    @111
    @62
    @92
    @93
    @98
    simpr2
    #
    @91
    cY
    @66
    frn
    syl
    #
    @106
    @66
    cfn
    wcel
    #
    @112
    @106
    @66
    @91
    wfn
    #
    @91
    cfn
    wcel
    #
    @115
    @106
    @93
    @116
    @113
    @91
    cY
    @66
    ffn
    syl
    #
    @106
    @43
    @92
    @117
    @62
    @43
    @99
    @81
    adantr
    @62
    @92
    @93
    @98
    simpr1
    #
    @4
    @91
    ssfi
    syl2anc
    @91
    @66
    fnfi
    syl2anc
    @66
    rnfi
    syl
    @107
    cY
    elfpw
    sylanbrc
    @106
    @109
    vz
    @107
    @76
    @47
    @15
    co
    #
    ciun
    #
    cY
    vx
    vz
    @107
    @48
    @120
    @5
    @76
    @47
    @15
    oveq1
    cbviunv
    @106
    @121
    cY
    @106
    @120
    cY
    wss
    #
    vz
    @107
    wral
    @121
    cY
    wss
    @106
    @122
    vz
    @107
    @106
    @76
    @107
    wcel
    #
    wa
    #
    cN
    cY
    cxmt
    cfv
    wcel
    #
    @76
    cY
    wcel
    @47
    cxr
    wcel
    #
    @122
    @124
    @24
    @125
    @2
    @24
    @53
    @61
    @99
    @123
    @25
    ad4antr
    cN
    cY
    metxmet
    syl
    @106
    @107
    cY
    @76
    @114
    sselda
    @53
    @126
    @2
    @61
    @99
    @123
    @47
    rpxr
    #
    ad4antlr
    cN
    @76
    @47
    cY
    blssm
    syl3anc
    ralrimiva
    vz
    @107
    @120
    cY
    iunss
    sylibr
    @106
    cY
    vy
    @4
    @88
    ciun
    #
    @121
    @106
    @128
    vy
    @4
    @70
    ciun
    #
    cY
    cin
    #
    cY
    vy
    @4
    cY
    @70
    iunin1
    @106
    cY
    @129
    wss
    @130
    cY
    wceq
    @106
    cY
    @57
    @129
    @54
    @30
    @58
    @99
    simplrr
    vx
    vy
    @4
    @56
    @70
    @89
    cbviunv
    syl6sseq
    cY
    @129
    sseqin2
    sylib
    syl5eq
    @106
    @88
    @121
    wss
    #
    vy
    @4
    wral
    @128
    @121
    wss
    @106
    @131
    vy
    @4
    @106
    @84
    wa
    #
    @131
    @88
    c0
    @88
    c0
    wceq
    #
    @131
    wi
    @132
    @133
    @131
    c0
    @121
    wss
    @121
    0ss
    @88
    c0
    @121
    sseq1
    mpbiri
    a1i
    @132
    @88
    c0
    wne
    #
    @103
    @131
    @106
    @98
    @84
    @134
    @103
    wi
    #
    @62
    @92
    @93
    @98
    simpr3
    @97
    @135
    vx
    @68
    @4
    @85
    @64
    @134
    @96
    @103
    @85
    @63
    @88
    c0
    @90
    neeq1d
    @85
    @5
    @68
    @95
    @102
    @85
    id
    @85
    @56
    @70
    @94
    @89
    imaeq2d
    eleq12d
    imbi12d
    rspccva
    sylan
    @132
    @103
    @131
    @106
    @103
    @131
    @84
    @106
    @103
    wa
    #
    @88
    @69
    @47
    @15
    co
    #
    @121
    @136
    @88
    @69
    @47
    @7
    co
    #
    cY
    cin
    #
    @137
    @136
    @70
    @138
    wss
    #
    @88
    @139
    wss
    @136
    @39
    @68
    cX
    wcel
    @47
    cr
    wcel
    @71
    @140
    @0
    @39
    @1
    @53
    @61
    @99
    @103
    @41
    ad5antr
    #
    @106
    @102
    cX
    @68
    @106
    @102
    @91
    cX
    @66
    @70
    cnvimass
    #
    @106
    @91
    @4
    cX
    @119
    @62
    @79
    @99
    @30
    @79
    @54
    @58
    @30
    @79
    @43
    @80
    simplbi
    ad2antrl
    adantr
    sstrd
    syl5ss
    sselda
    @136
    @47
    @2
    @53
    @61
    @99
    @103
    simp-4r
    rpred
    @106
    @116
    @103
    @71
    @118
    @116
    @103
    @68
    @91
    wcel
    #
    @71
    @91
    @68
    @70
    @66
    elpreima
    simplbda
    sylan
    @47
    cM
    cX
    @68
    @69
    blhalf
    syl22anc
    @70
    @138
    cY
    ssrin
    syl
    @136
    @39
    @69
    @40
    wcel
    @126
    @137
    @139
    wceq
    @141
    @136
    @69
    cY
    @40
    @106
    @93
    @143
    @69
    cY
    wcel
    @103
    @113
    @102
    @91
    @68
    @142
    sseli
    #
    @91
    cY
    @68
    @66
    ffvelrn
    syl2an
    @136
    @1
    @44
    @0
    @1
    @53
    @61
    @99
    @103
    simp-5r
    @45
    sylib
    eleqtrrd
    @53
    @126
    @2
    @61
    @99
    @103
    @127
    ad4antlr
    cN
    cM
    @69
    @47
    cX
    cY
    sstotbnd.2
    blres
    syl3anc
    sseqtr4d
    @136
    @69
    @107
    wcel
    #
    @137
    @121
    wss
    @106
    @116
    @143
    @145
    @103
    @118
    @144
    @91
    @68
    @66
    fnfvelrn
    syl2an
    vz
    @107
    @120
    @69
    @137
    @76
    @69
    @47
    @15
    oveq1
    ssiun2s
    syl
    sstrd
    adantlr
    ex
    syld
    pm2.61dne
    ralrimiva
    vy
    @4
    @88
    @121
    iunss
    sylibr
    eqsstr3d
    eqssd
    syl5eq
    @50
    @110
    vw
    @107
    @20
    @46
    @107
    wceq
    @49
    @109
    cY
    vx
    @46
    @107
    @48
    iuneq1
    eqeq1d
    rspcev
    syl2anc
    ex
    syld
    exlimdv
    mpd
    rexlimdvaa
    syld
    ralrimdva
    @2
    @24
    @3
    @52
    wb
    @25
    @3
    @24
    @52
    vx
    vw
    cN
    cY
    vc
    istotbnd3
    baib
    syl
    sylibrd
    impbid
end
