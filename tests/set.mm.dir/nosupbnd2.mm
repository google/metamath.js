include "csur.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wral.mm"
include "cdm.mm"
include "cres.mm"
include "wn.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "nfv.mm"
include "nfcv.mm"
include "crio.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "csuc.mm"
include "wceq.mm"
include "cab.mm"
include "cfv.mm"
include "cio.mm"
include "cmpt.mm"
include "cif.mm"
include "nfre1.mm"
include "nfriota1.mm"
include "nfdm.mm"
include "nfop.mm"
include "nfsn.mm"
include "nfun.mm"
include "nfiota1.mm"
include "nfmpt.mm"
include "nfif.mm"
include "nfcxfr.mm"
include "nfres.mm"
include "nfbr.mm"
include "nfn.mm"
include "nfim.mm"
include "simpl.mm"
include "wreu.mm"
include "wb.mm"
include "wrmo.mm"
include "rspe.mm"
include "adantr.mm"
include "nomaxmo.mm"
include "3ad2ant1.mm"
include "ad2antrl.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riota1.mm"
include "syl.mm"
include "mpbid.mm"
include "nosupbnd2lem1.mm"
include "3expb.mm"
include "dmeq.mm"
include "suceq.mm"
include "reseq2d.mm"
include "id.mm"
include "opeq1d.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "breq12d.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "con0.mm"
include "2on.mm"
include "elexi.mm"
include "dmsnop.mm"
include "uneq2i.mm"
include "dmun.mm"
include "df-suc.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"
include "mtbird.mm"
include "exp31.mm"
include "rexlimi.mm"
include "imp.mm"
include "nosupno.mm"
include "3adant3.mm"
include "nodmon.mm"
include "noreson.mm"
include "syl2anc.mm"
include "simprl3.mm"
include "cin.mm"
include "dmres.mm"
include "inss2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "inss1.mm"
include "nosupdm.mm"
include "abeq2d.mm"
include "simprl.mm"
include "simplrr.mm"
include "breq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "simprl1.mm"
include "sseldd.mm"
include "wor.mm"
include "sltso.mm"
include "soasym.mm"
include "mpan.mm"
include "simprrl.mm"
include "onelon.mm"
include "sucelon.mm"
include "sylib.mm"
include "sltres.mm"
include "syl3anc.mm"
include "mtod.mm"
include "simpll.mm"
include "simprl2.mm"
include "jca.mm"
include "simprrr.mm"
include "weq.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "nosupres.mm"
include "syl113anc.mm"
include "breq2d.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "word.mm"
include "nodmord.mm"
include "simpr.mm"
include "ordsucss.mm"
include "resabs1d.mm"
include "ralrimiva.mm"
include "noresle.mm"
include "syl23anc.mm"
include "wfun.mm"
include "wrel.mm"
include "nofun.mm"
include "funrel.mm"
include "resdm.mm"
include "3syl.mm"
include "mtbid.mm"
include "pm2.61ian.mm"
include "simpll1.mm"
include "simpll2.mm"
include "nosupbnd1.mm"
include "simplr.mm"
include "simpl1.mm"
include "sselda.mm"
include "simpll3.mm"
include "sotr3.mm"
include "mp2and.mm"
include "impbida.mm"

theorem nosupbnd2
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let vg: setvar g
  let cZ: class Z
  let va: setvar a
  let vp: setvar p
  let vq: setvar q
  assume nosupbnd2.1: |- S = if ( E. x e. A A. y e. A -. x <s y , ( ( iota_ x e. A A. y e. A -. x <s y ) u. { <. dom ( iota_ x e. A A. y e. A -. x <s y ) , 2o >. } ) , ( g e. { y | E. u e. A ( y e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc y ) = ( v |` suc y ) ) ) } |-> ( iota x E. u e. A ( g e. dom u /\ A. v e. A ( -. v <s u -> ( u |` suc g ) = ( v |` suc g ) ) /\ ( u ` g ) = x ) ) ) )

  disjoint A a
  disjoint a g
  disjoint A g
  disjoint a u
  disjoint A u
  disjoint a v
  disjoint A v
  disjoint a x
  disjoint A x
  disjoint a y
  disjoint A y
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint S a
  disjoint S g
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint Z a
  disjoint Z g
  disjoint Z x
  disjoint a p
  disjoint A p
  disjoint A q
  disjoint g p
  disjoint g q
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint q u
  disjoint q v
  disjoint q y
  disjoint S p
  disjoint Z p
  assert |- ( ( A C_ No /\ A e. _V /\ Z e. No ) -> ( A. a e. A a <s Z <-> -. ( Z |` dom S ) <s S ) )

  proof
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cZ
    csur
    wcel
    #
    w3a
    #
    va
    cv
    #
    cZ
    cslt
    wbr
    #
    va
    cA
    wral
    #
    cZ
    cS
    cdm
    #
    cres
    #
    cS
    cslt
    wbr
    #
    wn
    #
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
    @3
    @6
    wa
    #
    @10
    @14
    @15
    @10
    @13
    @15
    @10
    wi
    vx
    cA
    @15
    @10
    vx
    @15
    vx
    nfv
    @9
    vx
    vx
    @8
    cS
    cslt
    vx
    cZ
    @7
    vx
    cZ
    nfcv
    vx
    cS
    vx
    cS
    @14
    @13
    vx
    cA
    crio
    #
    @16
    cdm
    #
    c2o
    cop
    #
    csn
    #
    cun
    #
    vg
    @12
    vu
    cv
    #
    cdm
    #
    wcel
    vv
    cv
    #
    @21
    cslt
    wbr
    wn
    #
    @21
    @12
    csuc
    #
    cres
    @23
    @25
    cres
    wceq
    wi
    vv
    cA
    wral
    wa
    vu
    cA
    wrex
    vy
    cab
    #
    vg
    cv
    #
    @22
    wcel
    @24
    @21
    @27
    csuc
    #
    cres
    @23
    @28
    cres
    #
    wceq
    wi
    vv
    cA
    wral
    @27
    @21
    cfv
    @11
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
    cif
    #
    nosupbnd2.1
    @14
    vx
    @20
    @32
    @13
    vx
    cA
    nfre1
    vx
    @16
    @19
    @13
    vx
    cA
    nfriota1
    #
    vx
    @18
    vx
    @17
    c2o
    vx
    @16
    @34
    nfdm
    vx
    c2o
    nfcv
    nfop
    nfsn
    nfun
    vx
    vg
    @26
    @31
    vx
    @26
    nfcv
    @30
    vx
    nfiota1
    nfmpt
    nfif
    nfcxfr
    #
    nfdm
    nfres
    vx
    cslt
    nfcv
    @35
    nfbr
    nfn
    nfim
    @11
    cA
    wcel
    #
    @13
    @15
    @10
    @36
    @13
    wa
    #
    @15
    wa
    #
    @9
    cZ
    @17
    csuc
    #
    cres
    #
    @20
    cslt
    wbr
    #
    @38
    @16
    @11
    wceq
    #
    @41
    wn
    #
    @38
    @37
    @42
    @37
    @15
    simpl
    @38
    @13
    vx
    cA
    wreu
    #
    @37
    @42
    wb
    @38
    @14
    @13
    vx
    cA
    wrmo
    #
    @44
    @37
    @14
    @15
    @13
    vx
    cA
    rspe
    #
    adantr
    @3
    @45
    @37
    @6
    @0
    @1
    @45
    @2
    vx
    vy
    cA
    nomaxmo
    3ad2ant1
    ad2antrl
    @13
    vx
    cA
    reu5
    sylanbrc
    @13
    vx
    cA
    riota1
    syl
    mpbid
    @38
    @43
    @42
    cZ
    @11
    cdm
    #
    csuc
    #
    cres
    #
    @11
    @47
    c2o
    cop
    #
    csn
    #
    cun
    #
    cslt
    wbr
    #
    wn
    #
    @37
    @3
    @6
    @54
    vy
    cA
    @11
    cZ
    va
    nosupbnd2lem1
    3expb
    @42
    @41
    @53
    @42
    @40
    @49
    @20
    @52
    cslt
    @42
    @39
    @48
    cZ
    @42
    @17
    @47
    wceq
    @39
    @48
    wceq
    @16
    @11
    dmeq
    #
    @17
    @47
    suceq
    syl
    reseq2d
    @42
    @16
    @11
    @19
    @51
    @42
    id
    @42
    @18
    @50
    @42
    @17
    @47
    c2o
    @55
    opeq1d
    sneqd
    uneq12d
    breq12d
    notbid
    syl5ibrcom
    mpd
    @38
    @8
    @40
    cS
    @20
    cslt
    @37
    @8
    @40
    wceq
    @15
    @37
    @7
    @39
    cZ
    @37
    @7
    @20
    cdm
    #
    @39
    @37
    cS
    @20
    @37
    @14
    cS
    @20
    wceq
    #
    @46
    @14
    cS
    @33
    @20
    nosupbnd2.1
    @14
    @20
    @32
    iftrue
    syl5eq
    syl
    #
    dmeqd
    @17
    @19
    cdm
    #
    cun
    @17
    @17
    csn
    #
    cun
    @56
    @39
    @59
    @60
    @17
    @17
    c2o
    c2o
    con0
    2on
    elexi
    dmsnop
    uneq2i
    @16
    @19
    dmun
    @17
    df-suc
    3eqtr4i
    syl6eq
    reseq2d
    adantr
    @37
    @57
    @15
    @58
    adantr
    breq12d
    mtbird
    exp31
    rexlimi
    imp
    @14
    wn
    #
    @15
    wa
    #
    @8
    cS
    @7
    cres
    #
    cslt
    wbr
    #
    @9
    @62
    @63
    csur
    wcel
    #
    @8
    csur
    wcel
    #
    @63
    cdm
    #
    @7
    wss
    #
    @8
    cdm
    #
    @7
    wss
    #
    @8
    @28
    cres
    #
    @63
    @28
    cres
    #
    cslt
    wbr
    #
    wn
    #
    vg
    @7
    wral
    @64
    wn
    @62
    cS
    csur
    wcel
    #
    @7
    con0
    wcel
    #
    @65
    @3
    @75
    @61
    @6
    @0
    @1
    @75
    @2
    vx
    vy
    vv
    vu
    cA
    cS
    vg
    cvv
    nosupbnd2.1
    nosupno
    #
    3adant3
    ad2antrl
    #
    @62
    @75
    @76
    @78
    cS
    nodmon
    #
    syl
    #
    cS
    @7
    noreson
    syl2anc
    @62
    @2
    @76
    @66
    @0
    @1
    @2
    @6
    @61
    simprl3
    #
    @80
    cZ
    @7
    noreson
    #
    syl2anc
    @68
    @62
    @67
    @7
    @7
    cin
    @7
    cS
    @7
    dmres
    @7
    @7
    inss2
    eqsstri
    a1i
    @70
    @62
    @69
    @7
    cZ
    cdm
    #
    cin
    @7
    cZ
    @7
    dmres
    @7
    @83
    inss1
    eqsstri
    a1i
    @62
    @74
    vg
    @7
    @62
    @27
    @7
    wcel
    #
    wa
    #
    @73
    cZ
    @28
    cres
    #
    cS
    @28
    cres
    #
    cslt
    wbr
    #
    @62
    @84
    @88
    wn
    #
    @62
    @84
    @27
    vp
    cv
    #
    cdm
    #
    wcel
    #
    vq
    cv
    #
    @90
    cslt
    wbr
    #
    wn
    #
    @90
    @28
    cres
    #
    @93
    @28
    cres
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    wa
    #
    vp
    cA
    wrex
    #
    @89
    @61
    @84
    @102
    wb
    @15
    @61
    @102
    vg
    @7
    vx
    vy
    vg
    vv
    vu
    cA
    cS
    vg
    vq
    vp
    nosupbnd2.1
    nosupdm
    abeq2d
    adantr
    @62
    @101
    @89
    vp
    cA
    @62
    @90
    cA
    wcel
    #
    @101
    wa
    #
    wa
    #
    @88
    @86
    @96
    cslt
    wbr
    #
    @105
    @106
    cZ
    @90
    cslt
    wbr
    #
    @105
    @90
    cZ
    cslt
    wbr
    #
    @107
    wn
    #
    @105
    @103
    @6
    @108
    @62
    @103
    @101
    simprl
    #
    @61
    @3
    @6
    @104
    simplrr
    @5
    @108
    va
    @90
    cA
    @4
    @90
    cZ
    cslt
    breq1
    rspcv
    sylc
    @105
    @90
    csur
    wcel
    #
    @2
    @108
    @109
    wi
    #
    @105
    cA
    csur
    @90
    @62
    @0
    @104
    @0
    @1
    @2
    @6
    @61
    simprl1
    #
    adantr
    @110
    sseldd
    #
    @62
    @2
    @104
    @81
    adantr
    #
    csur
    cslt
    wor
    #
    @111
    @2
    wa
    @112
    sltso
    csur
    cslt
    @90
    cZ
    soasym
    mpan
    syl2anc
    mpd
    @105
    @2
    @111
    @28
    con0
    wcel
    #
    @106
    @107
    wi
    @115
    @114
    @105
    @27
    con0
    wcel
    #
    @117
    @105
    @91
    con0
    wcel
    #
    @92
    @118
    @105
    @111
    @119
    @114
    @90
    nodmon
    syl
    @62
    @103
    @92
    @100
    simprrl
    #
    @91
    @27
    onelon
    syl2anc
    @27
    sucelon
    sylib
    cZ
    @90
    @28
    sltres
    syl3anc
    mtod
    @105
    @87
    @96
    @86
    cslt
    @105
    @61
    @0
    @1
    wa
    #
    @103
    @92
    @23
    @90
    cslt
    wbr
    #
    wn
    #
    @96
    @29
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    @87
    @96
    wceq
    @61
    @15
    @104
    simpll
    @62
    @121
    @104
    @62
    @0
    @1
    @113
    @0
    @1
    @2
    @6
    @61
    simprl2
    jca
    adantr
    @110
    @120
    @105
    @100
    @126
    @62
    @103
    @92
    @100
    simprrr
    @125
    @99
    vv
    vq
    cA
    vv
    vq
    weq
    #
    @123
    @95
    @124
    @98
    @127
    @122
    @94
    @23
    @93
    @90
    cslt
    breq1
    notbid
    @127
    @29
    @97
    @96
    @23
    @93
    @28
    reseq1
    eqeq2d
    imbi12d
    cbvralv
    sylibr
    vx
    vy
    vv
    vu
    cA
    cS
    @90
    vg
    @27
    nosupbnd2.1
    nosupres
    syl113anc
    breq2d
    mtbird
    rexlimdvaa
    sylbid
    imp
    @85
    @71
    @86
    @72
    @87
    cslt
    @85
    cZ
    @28
    @7
    @85
    @7
    word
    #
    @84
    @28
    @7
    wss
    @85
    @75
    @128
    @62
    @75
    @84
    @78
    adantr
    cS
    nodmord
    syl
    @62
    @84
    simpr
    @27
    @7
    ordsucss
    sylc
    #
    resabs1d
    @85
    cS
    @28
    @7
    @129
    resabs1d
    breq12d
    mtbird
    ralrimiva
    @7
    @8
    @63
    vg
    noresle
    syl23anc
    @62
    @63
    cS
    @8
    cslt
    @62
    cS
    wfun
    #
    cS
    wrel
    @63
    cS
    wceq
    @62
    @75
    @130
    @78
    cS
    nofun
    syl
    cS
    funrel
    cS
    resdm
    3syl
    breq2d
    mtbid
    pm2.61ian
    @3
    @10
    wa
    #
    @5
    va
    cA
    @131
    @4
    cA
    wcel
    #
    wa
    #
    @4
    @7
    cres
    #
    @8
    cslt
    wbr
    #
    @5
    @133
    @134
    cS
    cslt
    wbr
    #
    @10
    @135
    @133
    @0
    @1
    @132
    @136
    @0
    @1
    @2
    @10
    @132
    simpll1
    #
    @0
    @1
    @2
    @10
    @132
    simpll2
    #
    @131
    @132
    simpr
    vx
    vy
    vv
    vu
    cA
    cS
    @4
    vg
    nosupbnd2.1
    nosupbnd1
    syl3anc
    @3
    @10
    @132
    simplr
    @133
    @134
    csur
    wcel
    #
    @75
    @66
    @136
    @10
    wa
    @135
    wi
    #
    @133
    @4
    csur
    wcel
    #
    @76
    @139
    @131
    cA
    csur
    @4
    @0
    @1
    @2
    @10
    simpl1
    sselda
    #
    @133
    @75
    @76
    @133
    @0
    @1
    @75
    @137
    @138
    @77
    syl2anc
    #
    @79
    syl
    #
    @4
    @7
    noreson
    syl2anc
    @143
    @133
    @2
    @76
    @66
    @0
    @1
    @2
    @10
    @132
    simpll3
    #
    @144
    @82
    syl2anc
    @116
    @139
    @75
    @66
    w3a
    @140
    sltso
    csur
    cslt
    @134
    cS
    @8
    sotr3
    mpan
    syl3anc
    mp2and
    @133
    @141
    @2
    @76
    @135
    @5
    wi
    @142
    @145
    @144
    @4
    cZ
    @7
    sltres
    syl3anc
    mpd
    ralrimiva
    impbida
end
