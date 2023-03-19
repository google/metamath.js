include "wcel.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "elex.mm"
include "wa.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "crio.mm"
include "cdm.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "cab.mm"
include "cfv.mm"
include "w3a.mm"
include "cio.mm"
include "cmpt.mm"
include "cif.mm"
include "iftrue.mm"
include "adantr.mm"
include "simprl.mm"
include "wreu.mm"
include "wrmo.mm"
include "simpl.mm"
include "nomaxmo.mm"
include "ad2antrl.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riotacl.mm"
include "syl.mm"
include "sseldd.mm"
include "c1o.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "noextend.mm"
include "eqeltrd.mm"
include "iffalse.mm"
include "wfun.mm"
include "crn.mm"
include "cpr.mm"
include "funmpt.mm"
include "a1i.mm"
include "iotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "word.mm"
include "wtr.mm"
include "ssel2.mm"
include "nodmon.mm"
include "onss.mm"
include "sseld.mm"
include "adantrd.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "wel.mm"
include "wal.mm"
include "simplr.mm"
include "adantlr.mm"
include "ontr1.mm"
include "mpand.mm"
include "reseq1.mm"
include "onelon.mm"
include "sylan.mm"
include "suceloni.mm"
include "simpllr.mm"
include "wb.mm"
include "eloni.mm"
include "ordsucelsuc.mm"
include "mpbid.mm"
include "onelss.mm"
include "sylc.mm"
include "resabs1d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "imim2d.mm"
include "ralimdv.mm"
include "expimpd.mm"
include "jcad.mm"
include "reximdva.mm"
include "vex.mm"
include "weq.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elab.mm"
include "anbi2i.mm"
include "3imtr4g.mm"
include "alrimivv.mm"
include "dftr2.mm"
include "sylibr.mm"
include "dford5.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "wfo.mm"
include "bdayfo.mm"
include "fofun.mm"
include "ax-mp.mm"
include "funimaexg.mm"
include "mpan.mm"
include "uniexg.mm"
include "adantl.mm"
include "reximi.mm"
include "ss2abi.mm"
include "bdayval.mm"
include "wfn.mm"
include "fofn.mm"
include "fnfvima.mm"
include "mp3an1.mm"
include "eqeltrrd.mm"
include "elssuni.mm"
include "syl5ss.mm"
include "ssexd.mm"
include "elong.mm"
include "mpbird.mm"
include "syl5eqel.mm"
include "rnmpt.mm"
include "weu.mm"
include "wex.mm"
include "wmo.mm"
include "fvex.mm"
include "eqeq2.mm"
include "3anbi3d.mm"
include "spcev.mm"
include "mp3an3.mm"
include "rexcom4.mm"
include "sylib.mm"
include "noprefixmo.mm"
include "eu5.mm"
include "iota2.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "simprr3.mm"
include "adantrr.mm"
include "norn.mm"
include "nofun.mm"
include "simprr1.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "sylbird.mm"
include "sylan2b.mm"
include "syl5eqss.mm"
include "elno2.mm"
include "syl3anbrc.mm"
include "pm2.61ian.mm"
include "sylan2.mm"

theorem nosupno
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let vg: setvar g
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume nosupno.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A x
  disjoint A y
  disjoint A g
  disjoint A v
  disjoint A u
  disjoint x y
  disjoint g x
  disjoint v x
  disjoint u x
  disjoint g y
  disjoint v y
  disjoint u y
  disjoint g v
  disjoint g u
  disjoint u v
  disjoint A a
  disjoint A b
  disjoint A z
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a g
  disjoint a v
  disjoint a u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b g
  disjoint b v
  disjoint b u
  disjoint x z
  disjoint y z
  disjoint g z
  disjoint v z
  disjoint u z
  assert |- ( ( A C_ No /\ A e. V ) -> S e. No )

  proof
    cA
    cV
    wcel
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cS
    csur
    wcel
    cA
    cV
    elex
    @0
    @1
    wa
    #
    cS
    vx
    cv
    #
    vy
    cv
    #
    cslt
    wbr
    wn
    vy
    cA
    wral
    #
    vx
    cA
    wrex
    #
    @5
    vx
    cA
    crio
    #
    @7
    cdm
    c2o
    cop
    csn
    cun
    #
    vg
    @4
    vu
    cv
    #
    cdm
    #
    wcel
    #
    vv
    cv
    #
    @9
    cslt
    wbr
    wn
    #
    @9
    @4
    csuc
    #
    cres
    #
    @12
    @14
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    vy
    cab
    #
    vg
    cv
    #
    @10
    wcel
    #
    @13
    @9
    @23
    csuc
    #
    cres
    #
    @12
    @25
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    @23
    @9
    cfv
    #
    @3
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cif
    #
    csur
    nosupno.1
    @6
    @2
    @37
    csur
    wcel
    @6
    @2
    wa
    #
    @37
    @8
    csur
    @6
    @37
    @8
    wceq
    @2
    @6
    @8
    @36
    iftrue
    adantr
    @38
    @7
    csur
    wcel
    @8
    csur
    wcel
    @38
    cA
    csur
    @7
    @6
    @0
    @1
    simprl
    @38
    @5
    vx
    cA
    wreu
    #
    @7
    cA
    wcel
    @38
    @6
    @5
    vx
    cA
    wrmo
    #
    @39
    @6
    @2
    simpl
    @0
    @40
    @6
    @1
    vx
    vy
    cA
    nomaxmo
    ad2antrl
    @5
    vx
    cA
    reu5
    sylanbrc
    @5
    vx
    cA
    riotacl
    syl
    sseldd
    @7
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    noextend
    syl
    eqeltrd
    @6
    wn
    #
    @2
    wa
    #
    @37
    @36
    csur
    @41
    @37
    @36
    wceq
    @2
    @6
    @8
    @36
    iffalse
    adantr
    @42
    @36
    wfun
    #
    @36
    cdm
    #
    con0
    wcel
    #
    @36
    crn
    #
    c1o
    c2o
    cpr
    #
    wss
    #
    @36
    csur
    wcel
    @43
    @42
    vg
    @22
    @35
    funmpt
    a1i
    @2
    @45
    @41
    @2
    @44
    @22
    con0
    vg
    @22
    @35
    @36
    @34
    vx
    iotaex
    @36
    eqid
    #
    dmmpti
    @2
    @22
    con0
    wcel
    #
    @22
    word
    #
    @0
    @51
    @1
    @0
    @22
    con0
    wss
    @22
    wtr
    #
    @51
    @0
    @21
    vy
    con0
    @0
    @20
    @4
    con0
    wcel
    #
    vu
    cA
    @0
    @9
    cA
    wcel
    #
    wa
    #
    @11
    @53
    @19
    @55
    @10
    con0
    @4
    @55
    @10
    con0
    wcel
    #
    @10
    con0
    wss
    @55
    @9
    csur
    wcel
    #
    @56
    cA
    csur
    @9
    ssel2
    #
    @9
    nodmon
    syl
    #
    @10
    onss
    syl
    sseld
    adantrd
    rexlimdva
    abssdv
    @0
    va
    vb
    wel
    #
    vb
    cv
    #
    @22
    wcel
    #
    wa
    #
    va
    cv
    #
    @22
    wcel
    #
    wi
    #
    vb
    wal
    va
    wal
    @52
    @0
    @66
    va
    vb
    @0
    @60
    @61
    @10
    wcel
    #
    @13
    @9
    @61
    csuc
    #
    cres
    #
    @12
    @68
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    wa
    @64
    @10
    wcel
    #
    @13
    @9
    @64
    csuc
    #
    cres
    #
    @12
    @77
    cres
    #
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    wa
    #
    vu
    cA
    wrex
    #
    @63
    @65
    @0
    @60
    @75
    @84
    @0
    @60
    wa
    #
    @74
    @83
    vu
    cA
    @85
    @54
    wa
    #
    @74
    @76
    @82
    @86
    @67
    @76
    @73
    @86
    @60
    @67
    @76
    @0
    @60
    @54
    simplr
    @86
    @56
    @60
    @67
    wa
    @76
    wi
    @0
    @54
    @56
    @60
    @59
    adantlr
    #
    @64
    @61
    @10
    ontr1
    syl
    mpand
    adantrd
    @86
    @67
    @73
    @82
    @86
    @67
    wa
    #
    @72
    @81
    vv
    cA
    @88
    @71
    @80
    @13
    @71
    @69
    @77
    cres
    #
    @70
    @77
    cres
    #
    wceq
    @88
    @80
    @69
    @70
    @77
    reseq1
    @88
    @89
    @78
    @90
    @79
    @88
    @9
    @77
    @68
    @88
    @68
    con0
    wcel
    #
    @77
    @68
    wcel
    #
    @77
    @68
    wss
    @88
    @61
    con0
    wcel
    #
    @91
    @86
    @56
    @67
    @93
    @87
    @10
    @61
    onelon
    sylan
    #
    @61
    suceloni
    syl
    @88
    @60
    @92
    @0
    @60
    @54
    @67
    simpllr
    @88
    @61
    word
    #
    @60
    @92
    wb
    @88
    @93
    @95
    @94
    @61
    eloni
    syl
    @64
    @61
    ordsucelsuc
    syl
    mpbid
    @68
    @77
    onelss
    sylc
    #
    resabs1d
    @88
    @12
    @77
    @68
    @96
    resabs1d
    eqeq12d
    syl5ib
    imim2d
    ralimdv
    expimpd
    jcad
    reximdva
    expimpd
    @62
    @75
    @60
    @21
    @75
    vy
    @61
    vb
    vex
    vy
    vb
    weq
    #
    @20
    @74
    vu
    cA
    @97
    @11
    @67
    @19
    @73
    @4
    @61
    @10
    eleq1
    @97
    @18
    @72
    vv
    cA
    @97
    @17
    @71
    @13
    @97
    @15
    @69
    @16
    @70
    @97
    @14
    @68
    @9
    @4
    @61
    suceq
    #
    reseq2d
    @97
    @14
    @68
    @12
    @98
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elab
    anbi2i
    @21
    @84
    vy
    @64
    va
    vex
    vy
    va
    weq
    #
    @20
    @83
    vu
    cA
    @99
    @11
    @76
    @19
    @82
    @4
    @64
    @10
    eleq1
    @99
    @18
    @81
    vv
    cA
    @99
    @17
    @80
    @13
    @99
    @15
    @78
    @16
    @79
    @99
    @14
    @77
    @9
    @4
    @64
    suceq
    #
    reseq2d
    @99
    @14
    @77
    @12
    @100
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elab
    3imtr4g
    alrimivv
    va
    vb
    @22
    dftr2
    sylibr
    @22
    dford5
    sylanbrc
    adantr
    @2
    @22
    cvv
    wcel
    @50
    @51
    wb
    @2
    @22
    cbday
    cA
    cima
    #
    cuni
    #
    cvv
    @1
    @102
    cvv
    wcel
    #
    @0
    @1
    @101
    cvv
    wcel
    #
    @103
    cbday
    wfun
    #
    @1
    @104
    csur
    con0
    cbday
    wfo
    #
    @105
    bdayfo
    csur
    con0
    cbday
    fofun
    ax-mp
    cbday
    cA
    cvv
    funimaexg
    mpan
    @101
    cvv
    uniexg
    syl
    adantl
    @2
    @22
    @11
    vu
    cA
    wrex
    #
    vy
    cab
    #
    @102
    @21
    @107
    vy
    @20
    @11
    vu
    cA
    @11
    @19
    simpl
    reximi
    ss2abi
    @0
    @108
    @102
    wss
    @1
    @0
    @107
    vy
    @102
    @0
    @11
    @4
    @102
    wcel
    vu
    cA
    @55
    @10
    @102
    @4
    @55
    @10
    @101
    wcel
    @10
    @102
    wss
    @55
    @9
    cbday
    cfv
    #
    @10
    @101
    @55
    @57
    @109
    @10
    wceq
    @58
    @9
    bdayval
    syl
    cbday
    csur
    wfn
    #
    @0
    @54
    @109
    @101
    wcel
    @106
    @110
    bdayfo
    csur
    con0
    cbday
    fofn
    ax-mp
    csur
    cA
    cbday
    @9
    fnfvima
    mp3an1
    eqeltrrd
    @10
    @101
    elssuni
    syl
    sseld
    rexlimdva
    abssdv
    adantr
    syl5ss
    ssexd
    @22
    cvv
    elong
    syl
    mpbird
    syl5eqel
    adantl
    @0
    @48
    @41
    @1
    @0
    @46
    vz
    cv
    #
    @35
    wceq
    #
    vg
    @22
    wrex
    #
    vz
    cab
    @47
    vg
    vz
    @22
    @35
    @36
    @49
    rnmpt
    @0
    @113
    vz
    @47
    @0
    @112
    @111
    @47
    wcel
    #
    vg
    @22
    @23
    @22
    wcel
    @0
    @24
    @30
    wa
    #
    vu
    cA
    wrex
    #
    @112
    @114
    wi
    @21
    @116
    vy
    @23
    vg
    vex
    vy
    vg
    weq
    #
    @20
    @115
    vu
    cA
    @117
    @11
    @24
    @19
    @30
    @4
    @23
    @10
    eleq1
    @117
    @18
    @29
    vv
    cA
    @117
    @17
    @28
    @13
    @117
    @15
    @26
    @16
    @27
    @117
    @14
    @25
    @9
    @4
    @23
    suceq
    #
    reseq2d
    @117
    @14
    @25
    @12
    @118
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    elab
    @0
    @116
    wa
    #
    @112
    @24
    @30
    @31
    @111
    wceq
    #
    w3a
    #
    vu
    cA
    wrex
    #
    @114
    @119
    @122
    @35
    @111
    wceq
    #
    @112
    @119
    @34
    vx
    weu
    #
    @122
    @123
    wb
    #
    @119
    @34
    vx
    wex
    #
    @34
    vx
    wmo
    #
    @124
    @116
    @126
    @0
    @116
    @33
    vx
    wex
    #
    vu
    cA
    wrex
    @126
    @115
    @128
    vu
    cA
    @24
    @30
    @31
    @31
    wceq
    #
    @128
    @31
    eqid
    @33
    @24
    @30
    @129
    w3a
    vx
    @31
    @23
    @9
    fvex
    @3
    @31
    wceq
    @32
    @129
    @24
    @30
    @3
    @31
    @31
    eqeq2
    3anbi3d
    spcev
    mp3an3
    reximi
    @33
    vu
    vx
    cA
    rexcom4
    sylib
    adantl
    @0
    @127
    @116
    vx
    vv
    vu
    cA
    @23
    noprefixmo
    adantr
    @34
    vx
    eu5
    sylanbrc
    @111
    cvv
    wcel
    @124
    @125
    vz
    vex
    @34
    @122
    vx
    @111
    cvv
    vx
    vz
    weq
    #
    @33
    @121
    vu
    cA
    @130
    @32
    @120
    @24
    @30
    @3
    @111
    @31
    eqeq2
    3anbi3d
    rexbidv
    iota2
    mpan
    syl
    @35
    @111
    eqcom
    syl6bb
    @0
    @122
    @114
    wi
    @116
    @0
    @121
    @114
    vu
    cA
    @0
    @54
    @121
    wa
    wa
    #
    @31
    @111
    @47
    @24
    @30
    @120
    @54
    @0
    simprr3
    @131
    @9
    crn
    #
    @47
    @31
    @131
    @57
    @132
    @47
    wss
    @0
    @54
    @57
    @121
    @58
    adantrr
    #
    @9
    norn
    syl
    @131
    @9
    wfun
    #
    @24
    @31
    @132
    wcel
    @131
    @57
    @134
    @133
    @9
    nofun
    syl
    @24
    @30
    @120
    @54
    @0
    simprr1
    @23
    @9
    fvelrn
    syl2anc
    sseldd
    eqeltrrd
    rexlimdvaa
    adantr
    sylbird
    sylan2b
    rexlimdva
    abssdv
    syl5eqss
    ad2antrl
    @36
    elno2
    syl3anbrc
    eqeltrd
    pm2.61ian
    syl5eqel
    sylan2
end
