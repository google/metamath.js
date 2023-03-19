include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "c0.mm"
include "cdif.mm"
include "cmpt.mm"
include "cima.mm"
include "cfi.mm"
include "cfv.mm"
include "wn.mm"
include "cint.mm"
include "wne.mm"
include "ccmp.mm"
include "ccld.mm"
include "wss.mm"
include "wb.mm"
include "elpwi.mm"
include "wa.mm"
include "ciin.mm"
include "0ss.mm"
include "0fin.mm"
include "elfpw.mm"
include "mpbir2an.mm"
include "simprr.mm"
include "simprl.mm"
include "unieqd.mm"
include "eqtrd.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "expr.mm"
include "cvv.mm"
include "vn0.mm"
include "iineq1.mm"
include "adantl.mm"
include "0iin.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "necon3bbid.mm"
include "mpbiri.mm"
include "pm2.21d.mm"
include "2thd.mm"
include "uniss.mm"
include "ad2antlr.mm"
include "eqss.mm"
include "baib.mm"
include "syl.mm"
include "eqcom.mm"
include "ssdif0.mm"
include "3bitr3g.mm"
include "ciun.mm"
include "iindif2.mm"
include "uniiun.mm"
include "difeq2i.mm"
include "syl6eqr.mm"
include "bitr4d.mm"
include "crn.mm"
include "imassrn.mm"
include "cres.mm"
include "df-ima.mm"
include "resmpt.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "syl5sseqr.mm"
include "wfun.mm"
include "funmpt.mm"
include "simprbi.mm"
include "imafi.mm"
include "sylanbrc.mm"
include "wfn.mm"
include "eqid.mm"
include "topopn.mm"
include "difexg.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "sylib.mm"
include "simpld.mm"
include "sseqtrd.mm"
include "simprd.mm"
include "fipreima.mm"
include "syl3anc.mm"
include "rexbii.mm"
include "inteqd.mm"
include "rexxfrd.mm"
include "0ex.mm"
include "wfo.mm"
include "wf1o.mm"
include "ccnv.mm"
include "opncldf1.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseq.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elfi.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "inundif.mm"
include "rexeqi.mm"
include "rexun.mm"
include "bitr3i.mm"
include "inss2.mm"
include "sseli.mm"
include "elsni.mm"
include "uni0.mm"
include "biimpd.mm"
include "rexlimiv.mm"
include "ssid.mm"
include "a1i.mm"
include "syl6eqss.mm"
include "eqssd.mm"
include "eqtr3d.mm"
include "syl6eqel.mm"
include "pwfi.mm"
include "pwuni.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eldifsn.mm"
include "syl2anc.mm"
include "syl5.mm"
include "idd.mm"
include "jaod.mm"
include "olc.mm"
include "impbid1.mm"
include "syl5bb.mm"
include "eldifi.mm"
include "simpllr.mm"
include "sstrd.mm"
include "unissd.mm"
include "bitri.mm"
include "resmptd.mm"
include "dfiin3g.mm"
include "3eqtr2d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "imaeq2.mm"
include "ima0.mm"
include "int0.mm"
include "neeq1d.mm"
include "necomd.mm"
include "necon2i.mm"
include "rbaibr.mm"
include "pm5.32ri.mm"
include "rexbii2.mm"
include "syl6bbr.mm"
include "3bitr4rd.mm"
include "imbi12d.mm"
include "pm2.61dane.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "nne.mm"
include "imbi1d.mm"
include "con1b.mm"
include "syl6bb.mm"
include "sylan2.mm"
include "ralbidva.mm"
include "iscmp.mm"
include "wex.mm"
include "simpl.mm"
include "foima.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "ssimaexg.mm"
include "df-rex.mm"
include "selpw.mm"
include "anbi1i.mm"
include "exbii.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ralxfrd.mm"
include "3bitr4d.mm"

theorem cmpfi
  let vx: setvar x
  let cJ: class J
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint J x
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint J r
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  assert |- ( J e. Top -> ( J e. Comp <-> A. x e. ~P ( Clsd ` J ) ( -. (/) e. ( fi ` x ) -> |^| x =/= (/) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    @1
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @2
    cpw
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    cJ
    cpw
    #
    wral
    #
    c0
    vr
    cJ
    @1
    vr
    cv
    #
    cdif
    #
    cmpt
    #
    @2
    cima
    #
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    @16
    cint
    #
    c0
    wne
    #
    wi
    #
    vy
    @11
    wral
    cJ
    ccmp
    wcel
    #
    c0
    vx
    cv
    #
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    @24
    cint
    #
    c0
    wne
    #
    wi
    #
    vx
    cJ
    ccld
    cfv
    #
    cpw
    #
    wral
    @0
    @10
    @22
    vy
    @11
    @2
    @11
    wcel
    #
    @0
    @2
    cJ
    wss
    #
    @10
    @22
    wb
    @2
    cJ
    elpwi
    @0
    @34
    wa
    #
    @10
    @21
    wn
    #
    @18
    wi
    #
    @22
    @35
    @10
    vr
    @2
    @14
    ciin
    #
    c0
    wceq
    #
    @18
    wi
    #
    @37
    @35
    @10
    @40
    wb
    @2
    c0
    @35
    @2
    c0
    wceq
    #
    wa
    #
    @10
    @40
    @35
    @41
    @4
    @9
    @35
    @41
    @4
    wa
    wa
    #
    c0
    @8
    wcel
    #
    @1
    c0
    cuni
    #
    wceq
    #
    @9
    @44
    c0
    @2
    wss
    c0
    cfn
    wcel
    @2
    0ss
    0fin
    c0
    @2
    elfpw
    mpbir2an
    @43
    @1
    @3
    @45
    @35
    @41
    @4
    simprr
    @43
    @2
    c0
    @35
    @41
    @4
    simprl
    unieqd
    eqtrd
    @7
    @46
    vz
    c0
    @8
    @5
    c0
    wceq
    #
    @6
    @45
    @1
    @5
    c0
    unieq
    eqeq2d
    rspcev
    sylancr
    expr
    @42
    @39
    @18
    @42
    @39
    wn
    cvv
    c0
    wne
    #
    vn0
    @42
    @39
    cvv
    c0
    @42
    @38
    cvv
    c0
    @42
    @38
    vr
    c0
    @14
    ciin
    #
    cvv
    @41
    @38
    @49
    wceq
    @35
    vr
    @2
    c0
    @14
    iineq1
    adantl
    vr
    @14
    0iin
    syl6eq
    eqeq1d
    necon3bbid
    mpbiri
    pm2.21d
    2thd
    @35
    @2
    c0
    wne
    #
    wa
    #
    @4
    @39
    @9
    @18
    @51
    @4
    @1
    @3
    cdif
    #
    c0
    wceq
    #
    @39
    @51
    @3
    @1
    wceq
    #
    @1
    @3
    wss
    #
    @4
    @53
    @51
    @3
    @1
    wss
    #
    @54
    @55
    wb
    @34
    @56
    @0
    @50
    @2
    cJ
    uniss
    #
    ad2antlr
    @54
    @56
    @55
    @3
    @1
    eqss
    baib
    syl
    @3
    @1
    eqcom
    @1
    @3
    ssdif0
    3bitr3g
    @51
    @38
    @52
    c0
    @51
    @38
    @1
    vr
    @2
    @13
    ciun
    #
    cdif
    #
    @52
    @50
    @38
    @59
    wceq
    @35
    vr
    @2
    @1
    @13
    iindif2
    adantl
    @3
    @58
    @1
    vr
    @2
    uniiun
    difeq2i
    syl6eqr
    eqeq1d
    bitr4d
    @51
    c0
    vw
    cv
    #
    cint
    #
    wceq
    #
    vw
    @16
    cpw
    cfn
    cin
    #
    wrex
    #
    c0
    vr
    @2
    @14
    cmpt
    #
    @5
    cima
    #
    cint
    #
    wceq
    #
    vz
    @8
    wrex
    #
    @18
    @9
    @51
    @62
    @68
    vw
    vz
    @66
    @63
    @8
    @51
    @5
    @8
    wcel
    #
    wa
    #
    @66
    @16
    wss
    @66
    cfn
    wcel
    #
    @66
    @63
    wcel
    @71
    @65
    crn
    #
    @66
    @16
    @65
    @5
    imassrn
    @35
    @16
    @73
    wceq
    #
    @50
    @70
    @35
    @16
    @15
    @2
    cres
    #
    crn
    @73
    @15
    @2
    df-ima
    @35
    @75
    @65
    @34
    @75
    @65
    wceq
    @0
    vr
    cJ
    @2
    @14
    resmpt
    adantl
    rneqd
    syl5eq
    #
    ad2antrr
    syl5sseqr
    @71
    @65
    wfun
    @5
    cfn
    wcel
    #
    @72
    vr
    @2
    @14
    funmpt
    @70
    @77
    @51
    @70
    @5
    @2
    wss
    #
    @77
    @5
    @2
    elfpw
    #
    simprbi
    adantl
    @65
    @5
    imafi
    sylancr
    @66
    @16
    elfpw
    sylanbrc
    @51
    @60
    @63
    wcel
    #
    wa
    #
    @66
    @60
    wceq
    #
    vz
    @8
    wrex
    #
    @60
    @66
    wceq
    #
    vz
    @8
    wrex
    @81
    @65
    @2
    wfn
    #
    @60
    @73
    wss
    @60
    cfn
    wcel
    #
    @83
    @0
    @85
    @34
    @50
    @80
    @0
    @14
    cvv
    wcel
    #
    vr
    @2
    wral
    #
    @85
    @0
    @87
    vr
    @2
    @0
    @1
    cJ
    wcel
    @87
    cJ
    @1
    @1
    eqid
    #
    topopn
    @1
    @13
    cJ
    difexg
    syl
    #
    ralrimivw
    #
    vr
    @2
    @14
    @65
    cvv
    @65
    eqid
    fnmpt
    syl
    ad3antrrr
    @81
    @60
    @16
    @73
    @81
    @60
    @16
    wss
    #
    @86
    @81
    @80
    @92
    @86
    wa
    @51
    @80
    simpr
    @60
    @16
    elfpw
    sylib
    #
    simpld
    @35
    @74
    @50
    @80
    @76
    ad2antrr
    sseqtrd
    @81
    @92
    @86
    @93
    simprd
    @60
    @2
    @65
    vz
    fipreima
    syl3anc
    @82
    @84
    vz
    @8
    @66
    @60
    eqcom
    rexbii
    sylib
    @51
    @84
    wa
    #
    @61
    @67
    c0
    @94
    @60
    @66
    @51
    @84
    simpr
    inteqd
    eqeq2d
    rexxfrd
    @51
    c0
    cvv
    wcel
    @16
    @32
    wcel
    #
    @18
    @64
    wb
    0ex
    @0
    @95
    @34
    @50
    @0
    @16
    @31
    wss
    @95
    @0
    @15
    crn
    #
    @16
    @31
    @15
    @2
    imassrn
    @0
    cJ
    @31
    @15
    wfo
    #
    @96
    @31
    wceq
    @0
    cJ
    @31
    @15
    wf1o
    #
    @97
    @0
    @98
    @15
    ccnv
    vv
    @31
    @1
    vv
    cv
    cdif
    cmpt
    wceq
    vv
    vr
    @15
    cJ
    @1
    @89
    @15
    eqid
    opncldf1
    simpld
    cJ
    @31
    @15
    f1ofo
    syl
    #
    cJ
    @31
    @15
    forn
    syl
    syl5sseq
    @16
    @31
    cJ
    ccld
    fvex
    elpw2
    sylibr
    #
    ad2antrr
    vw
    c0
    @16
    cvv
    @32
    elfi
    sylancr
    @51
    @9
    @68
    vz
    @8
    c0
    csn
    #
    cdif
    #
    wrex
    #
    @69
    @51
    @9
    @7
    vz
    @102
    wrex
    #
    @103
    @9
    @7
    vz
    @8
    @101
    cin
    #
    wrex
    #
    @104
    wo
    #
    @51
    @104
    @9
    @7
    vz
    @105
    @102
    cun
    #
    wrex
    @107
    @7
    vz
    @108
    @8
    @8
    @101
    inundif
    rexeqi
    @7
    vz
    @105
    @102
    rexun
    bitr3i
    @51
    @107
    @104
    @51
    @106
    @104
    @104
    @106
    @1
    c0
    wceq
    #
    @51
    @104
    @7
    @109
    vz
    @105
    @5
    @105
    wcel
    #
    @7
    @109
    @110
    @6
    c0
    @1
    @110
    @6
    @45
    c0
    @110
    @5
    c0
    @110
    @5
    @101
    wcel
    @47
    @105
    @101
    @5
    @8
    @101
    inss2
    sseli
    @5
    c0
    elsni
    syl
    unieqd
    uni0
    syl6eq
    eqeq2d
    biimpd
    rexlimiv
    @35
    @50
    @109
    @104
    @35
    @50
    @109
    wa
    #
    wa
    #
    @2
    @102
    wcel
    #
    @4
    @104
    @112
    @2
    @8
    wcel
    #
    @50
    @113
    @112
    @2
    @2
    wss
    #
    @2
    cfn
    wcel
    #
    @114
    @115
    @112
    @2
    ssid
    a1i
    @112
    @3
    cpw
    #
    cfn
    wcel
    #
    @2
    @117
    wss
    @116
    @112
    @3
    cfn
    wcel
    @118
    @112
    @3
    c0
    cfn
    @112
    @1
    @3
    c0
    @112
    @1
    @3
    @112
    @1
    c0
    @3
    @35
    @50
    @109
    simprr
    #
    @3
    0ss
    syl6eqss
    @34
    @56
    @0
    @111
    @57
    ad2antlr
    eqssd
    #
    @119
    eqtr3d
    0fin
    syl6eqel
    @3
    pwfi
    sylib
    @2
    pwuni
    @117
    @2
    ssfi
    sylancl
    @2
    @2
    elfpw
    sylanbrc
    @35
    @50
    @109
    simprl
    @2
    @8
    c0
    eldifsn
    sylanbrc
    @120
    @7
    @4
    vz
    @2
    @102
    @5
    @2
    wceq
    @6
    @3
    @1
    @5
    @2
    unieq
    eqeq2d
    rspcev
    syl2anc
    expr
    syl5
    @51
    @104
    idd
    jaod
    @104
    @106
    olc
    impbid1
    syl5bb
    @51
    @7
    @68
    vz
    @102
    @51
    @5
    @102
    wcel
    #
    wa
    #
    @7
    c0
    @1
    @6
    cdif
    #
    wceq
    #
    @68
    @122
    @6
    @1
    wceq
    #
    @1
    @6
    wss
    #
    @7
    @124
    @122
    @6
    @1
    wss
    #
    @125
    @126
    wb
    @122
    @5
    cJ
    @122
    @5
    @2
    cJ
    @122
    @78
    @77
    @122
    @70
    @78
    @77
    wa
    @121
    @70
    @51
    @5
    @8
    @101
    eldifi
    adantl
    @79
    sylib
    simpld
    #
    @0
    @34
    @50
    @121
    simpllr
    sstrd
    unissd
    @125
    @127
    @126
    @6
    @1
    eqss
    baib
    syl
    @6
    @1
    eqcom
    @126
    @123
    c0
    wceq
    @124
    @1
    @6
    ssdif0
    @123
    c0
    eqcom
    bitri
    3bitr3g
    @122
    @67
    @123
    c0
    @122
    @67
    @1
    vr
    @5
    @13
    ciun
    #
    cdif
    #
    @123
    @122
    @67
    vr
    @5
    @14
    cmpt
    #
    crn
    #
    cint
    #
    vr
    @5
    @14
    ciin
    #
    @130
    @122
    @66
    @132
    @122
    @66
    @65
    @5
    cres
    #
    crn
    @132
    @65
    @5
    df-ima
    @122
    @135
    @131
    @122
    vr
    @2
    @5
    @14
    @128
    resmptd
    rneqd
    syl5eq
    inteqd
    @122
    @87
    vr
    @5
    wral
    #
    @134
    @133
    wceq
    @0
    @136
    @34
    @50
    @121
    @0
    @87
    vr
    @5
    @90
    ralrimivw
    ad3antrrr
    vr
    @5
    @14
    cvv
    dfiin3g
    syl
    @122
    @5
    c0
    wne
    #
    @134
    @130
    wceq
    @121
    @137
    @51
    @121
    @70
    @137
    @5
    @8
    c0
    eldifsn
    #
    simprbi
    adantl
    vr
    @5
    @1
    @13
    iindif2
    syl
    3eqtr2d
    @6
    @129
    @1
    vr
    @5
    uniiun
    difeq2i
    syl6eqr
    eqeq2d
    bitr4d
    rexbidva
    bitrd
    @68
    @68
    vz
    @8
    @102
    @68
    @70
    @121
    @68
    @137
    @70
    @121
    wb
    @5
    c0
    c0
    @67
    @47
    @67
    c0
    @47
    @67
    c0
    wne
    @48
    vn0
    @47
    @67
    cvv
    c0
    @47
    @67
    c0
    cint
    cvv
    @47
    @66
    c0
    @47
    @66
    @65
    c0
    cima
    c0
    @5
    c0
    @65
    imaeq2
    @65
    ima0
    syl6eq
    inteqd
    int0
    syl6eq
    neeq1d
    mpbiri
    necomd
    necon2i
    @121
    @70
    @137
    @138
    rbaibr
    syl
    pm5.32ri
    rexbii2
    syl6bbr
    3bitr4rd
    imbi12d
    pm2.61dane
    @35
    @39
    @36
    @18
    @35
    @39
    @20
    c0
    wceq
    @36
    @35
    @38
    @20
    c0
    @35
    @38
    @73
    cint
    #
    @20
    @35
    @88
    @38
    @139
    wceq
    @0
    @88
    @34
    @91
    adantr
    vr
    @2
    @14
    cvv
    dfiin3g
    syl
    @35
    @16
    @73
    @76
    inteqd
    eqtr4d
    eqeq1d
    @20
    c0
    nne
    syl6bbr
    imbi1d
    bitrd
    @21
    @18
    con1b
    syl6bb
    sylan2
    ralbidva
    @23
    @0
    @12
    vy
    vz
    cJ
    @1
    @89
    iscmp
    baib
    @0
    @30
    @22
    vx
    vy
    @16
    @32
    @11
    @0
    @95
    @33
    @100
    adantr
    @0
    @24
    @32
    wcel
    #
    wa
    #
    @34
    @24
    @16
    wceq
    #
    wa
    #
    vy
    wex
    #
    @142
    vy
    @11
    wrex
    #
    @141
    @0
    @15
    wfun
    #
    @24
    @15
    cJ
    cima
    #
    wss
    #
    @144
    @0
    @140
    simpl
    @146
    @141
    vr
    cJ
    @14
    funmpt
    a1i
    @0
    @140
    @148
    @140
    @148
    @0
    @24
    @31
    wss
    @24
    @31
    elpwi
    @0
    @147
    @31
    @24
    @0
    @97
    @147
    @31
    wceq
    @99
    cJ
    @31
    @15
    foima
    syl
    sseq2d
    syl5ibr
    imp
    vy
    cJ
    @24
    ctop
    @15
    ssimaexg
    syl3anc
    @145
    @33
    @142
    wa
    #
    vy
    wex
    @144
    @142
    vy
    @11
    df-rex
    @149
    @143
    vy
    @33
    @34
    @142
    vy
    cJ
    selpw
    anbi1i
    exbii
    bitri
    sylibr
    @0
    @142
    wa
    #
    @27
    @19
    @29
    @21
    @150
    @26
    @18
    @150
    @25
    @17
    c0
    @150
    @24
    @16
    cfi
    @0
    @142
    simpr
    #
    fveq2d
    eleq2d
    notbid
    @150
    @28
    @20
    c0
    @150
    @24
    @16
    @151
    inteqd
    neeq1d
    imbi12d
    ralxfrd
    3bitr4d
end
