include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cdm.mm"
include "cres.mm"
include "csuc.mm"
include "con0.mm"
include "simp2l.mm"
include "simp3.mm"
include "sseldd.mm"
include "nosupno.mm"
include "3ad2ant2.mm"
include "nodmon.mm"
include "syl.mm"
include "noreson.mm"
include "syl2anc.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "a1i.mm"
include "ssid.mm"
include "wceq.mm"
include "wi.mm"
include "wb.mm"
include "cab.mm"
include "cfv.mm"
include "cio.mm"
include "cmpt.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cif.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "iotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "vex.mm"
include "weq.mm"
include "eleq1.mm"
include "suceq.mm"
include "reseq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "dmeq.mm"
include "breq2.mm"
include "notbid.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "elab.mm"
include "3ad2ant1.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "nosupres.mm"
include "syl113anc.mm"
include "simpl2l.mm"
include "adantr.mm"
include "wor.mm"
include "sltso.mm"
include "soasym.mm"
include "mpan.mm"
include "simpl3.mm"
include "breq1.mm"
include "eqeq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "syld.mm"
include "imp.mm"
include "onelon.mm"
include "sucelon.mm"
include "sylib.mm"
include "sonr.mm"
include "eqnbrtrd.mm"
include "ex.mm"
include "sltres.mm"
include "syl3anc.mm"
include "con3d.mm"
include "pm2.61d.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "word.mm"
include "nodmord.mm"
include "ordsucss.mm"
include "3syl.mm"
include "resabs1d.mm"
include "breq2d.mm"
include "mtbird.mm"
include "ralrimiva.mm"
include "noresle.mm"
include "syl23anc.mm"

theorem nosupbnd1lem1
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let vp: setvar p
  assume nosupbnd1.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A g
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint u v
  disjoint U v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A h
  disjoint A p
  disjoint h p
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint S h
  disjoint S p
  disjoint U h
  disjoint U p
  assert |- ( ( -. E. x e. A A. y e. A -. x <s y /\ ( A C_ No /\ A e. _V ) /\ U e. A ) -> -. S <s ( U |` dom S ) )

  proof
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
    wn
    #
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cU
    cA
    wcel
    #
    w3a
    #
    cU
    cS
    cdm
    #
    cres
    #
    csur
    wcel
    #
    cS
    csur
    wcel
    #
    @11
    cdm
    #
    @10
    wss
    #
    @10
    @10
    wss
    #
    cS
    vh
    cv
    #
    csuc
    #
    cres
    #
    @11
    @18
    cres
    #
    cslt
    wbr
    #
    wn
    #
    vh
    @10
    wral
    cS
    @11
    cslt
    wbr
    wn
    @9
    cU
    csur
    wcel
    #
    @10
    con0
    wcel
    #
    @12
    @9
    cA
    csur
    cU
    @4
    @5
    @6
    @8
    simp2l
    @4
    @7
    @8
    simp3
    sseldd
    #
    @9
    @13
    @24
    @7
    @4
    @13
    @8
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    nosupbnd1.1
    nosupno
    3ad2ant2
    #
    cS
    nodmon
    syl
    cU
    @10
    noreson
    syl2anc
    @26
    @15
    @9
    @14
    @10
    cU
    cdm
    #
    cin
    @10
    cU
    @10
    dmres
    @10
    @27
    inss1
    eqsstri
    a1i
    @16
    @9
    @10
    ssid
    a1i
    @9
    @22
    vh
    @10
    @9
    @17
    @10
    wcel
    #
    wa
    #
    @21
    @19
    cU
    @18
    cres
    #
    cslt
    wbr
    #
    @9
    @28
    @31
    wn
    #
    @9
    @28
    @17
    vp
    cv
    #
    cdm
    #
    wcel
    #
    vv
    cv
    #
    @33
    cslt
    wbr
    #
    wn
    #
    @33
    @18
    cres
    #
    @36
    @18
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
    vp
    cA
    wrex
    #
    @32
    @4
    @7
    @28
    @45
    wb
    @8
    @4
    @28
    @17
    @1
    vu
    cv
    #
    cdm
    #
    wcel
    #
    @36
    @46
    cslt
    wbr
    #
    wn
    #
    @46
    @1
    csuc
    #
    cres
    #
    @36
    @51
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
    wcel
    @45
    @4
    @10
    @59
    @17
    @4
    @10
    vg
    @59
    vg
    cv
    #
    @47
    wcel
    @50
    @46
    @60
    csuc
    #
    cres
    @36
    @61
    cres
    wceq
    wi
    vv
    cA
    wral
    @60
    @46
    cfv
    @0
    wceq
    w3a
    vu
    cA
    wrex
    #
    vx
    cio
    #
    cmpt
    #
    cdm
    @59
    @4
    cS
    @64
    @4
    cS
    @3
    @2
    vx
    cA
    crio
    #
    @65
    cdm
    c2o
    cop
    csn
    cun
    #
    @64
    cif
    @64
    nosupbnd1.1
    @3
    @66
    @64
    iffalse
    syl5eq
    dmeqd
    vg
    @59
    @63
    @64
    @62
    vx
    iotaex
    @64
    eqid
    dmmpti
    syl6eq
    eleq2d
    @58
    @45
    vy
    @17
    vh
    vex
    vy
    vh
    weq
    #
    @58
    @17
    @47
    wcel
    #
    @50
    @46
    @18
    cres
    #
    @40
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
    @45
    @67
    @57
    @73
    vu
    cA
    @67
    @48
    @68
    @56
    @72
    @1
    @17
    @47
    eleq1
    @67
    @55
    @71
    vv
    cA
    @67
    @54
    @70
    @50
    @67
    @52
    @69
    @53
    @40
    @67
    @51
    @18
    @46
    @1
    @17
    suceq
    #
    reseq2d
    @67
    @51
    @18
    @36
    @74
    reseq2d
    eqeq12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    @73
    @44
    vu
    vp
    cA
    vu
    vp
    weq
    #
    @68
    @35
    @72
    @43
    @75
    @47
    @34
    @17
    @46
    @33
    dmeq
    eleq2d
    @75
    @71
    @42
    vv
    cA
    @75
    @50
    @38
    @70
    @41
    @75
    @49
    @37
    @46
    @33
    @36
    cslt
    breq2
    notbid
    @75
    @69
    @39
    @40
    @46
    @33
    @18
    reseq1
    eqeq1d
    imbi12d
    ralbidv
    anbi12d
    cbvrexv
    syl6bb
    elab
    syl6bb
    3ad2ant1
    @9
    @44
    @32
    vp
    cA
    @9
    @33
    cA
    wcel
    #
    @44
    wa
    #
    wa
    #
    @19
    @39
    @30
    cslt
    @78
    @4
    @7
    @76
    @35
    @43
    @19
    @39
    wceq
    @4
    @7
    @8
    @77
    simpl1
    @4
    @7
    @8
    @77
    simpl2
    @9
    @76
    @44
    simprl
    #
    @9
    @76
    @35
    @43
    simprrl
    #
    @9
    @76
    @35
    @43
    simprrr
    #
    vx
    vy
    vv
    vu
    cA
    cS
    @33
    vg
    @17
    nosupbnd1.1
    nosupres
    syl113anc
    @78
    @33
    cU
    cslt
    wbr
    #
    @39
    @30
    cslt
    wbr
    #
    wn
    #
    @78
    @82
    @84
    @78
    @82
    wa
    @39
    @30
    @30
    cslt
    @78
    @82
    @39
    @30
    wceq
    #
    @78
    @82
    cU
    @33
    cslt
    wbr
    #
    wn
    #
    @85
    @78
    @33
    csur
    wcel
    #
    @23
    @82
    @87
    wi
    #
    @78
    cA
    csur
    @33
    @5
    @6
    @4
    @8
    @77
    simpl2l
    @79
    sseldd
    #
    @9
    @23
    @77
    @25
    adantr
    #
    csur
    cslt
    wor
    #
    @88
    @23
    wa
    @89
    sltso
    csur
    cslt
    @33
    cU
    soasym
    mpan
    syl2anc
    @78
    @8
    @43
    @87
    @85
    wi
    #
    @4
    @7
    @8
    @77
    simpl3
    @81
    @42
    @93
    vv
    cU
    cA
    @36
    cU
    wceq
    #
    @38
    @87
    @41
    @85
    @94
    @37
    @86
    @36
    cU
    @33
    cslt
    breq1
    notbid
    @94
    @40
    @30
    @39
    @36
    cU
    @18
    reseq1
    eqeq2d
    imbi12d
    rspcv
    sylc
    syld
    imp
    @78
    @30
    @30
    cslt
    wbr
    wn
    #
    @82
    @78
    @30
    csur
    wcel
    #
    @95
    @78
    @23
    @18
    con0
    wcel
    #
    @96
    @91
    @78
    @17
    con0
    wcel
    #
    @97
    @78
    @34
    con0
    wcel
    #
    @35
    @98
    @78
    @88
    @99
    @90
    @33
    nodmon
    syl
    @80
    @34
    @17
    onelon
    syl2anc
    @17
    sucelon
    sylib
    #
    cU
    @18
    noreson
    syl2anc
    @92
    @96
    @95
    sltso
    csur
    @30
    cslt
    sonr
    mpan
    syl
    adantr
    eqnbrtrd
    ex
    @78
    @83
    @82
    @78
    @88
    @23
    @97
    @83
    @82
    wi
    @90
    @91
    @100
    @33
    cU
    @18
    sltres
    syl3anc
    con3d
    pm2.61d
    eqnbrtrd
    rexlimdvaa
    sylbid
    imp
    @29
    @20
    @30
    @19
    cslt
    @29
    cU
    @18
    @10
    @9
    @28
    @18
    @10
    wss
    #
    @9
    @13
    @10
    word
    @28
    @101
    wi
    @26
    cS
    nodmord
    @17
    @10
    ordsucss
    3syl
    imp
    resabs1d
    breq2d
    mtbird
    ralrimiva
    @10
    cS
    @11
    vh
    noresle
    syl23anc
end
