include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "wf1.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wf.mm"
include "wsmo.mm"
include "w3a.mm"
include "cff1.mm"
include "cfon.mm"
include "oneli.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "weq.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "wel.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ontr1.mm"
include "ax-mp.mm"
include "ancoms.mm"
include "3ad2antl3.mm"
include "pm2.27.mm"
include "syl3anc.mm"
include "ralimdva.mm"
include "crecs.mm"
include "csuc.mm"
include "ciun.mm"
include "cun.mm"
include "wceq.mm"
include "cres.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"
include "cdm.mm"
include "recsval.mm"
include "cvv.mm"
include "wfun.mm"
include "wfn.mm"
include "recsfnon.mm"
include "fnfun.mm"
include "vex.mm"
include "resfunexg.mm"
include "mp2an.mm"
include "dmeq.mm"
include "fveq2d.mm"
include "fveq1.mm"
include "suceq.mm"
include "syl.mm"
include "iuneq12d.mm"
include "uneq12d.mm"
include "fvex.mm"
include "dmex.mm"
include "sucex.mm"
include "iunex.mm"
include "unex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "onss.mm"
include "fnssres.mm"
include "sylancr.mm"
include "fndm.mm"
include "iuneq1.mm"
include "iuneq2i.mm"
include "cbviunv.mm"
include "eqtr4i.mm"
include "3syl.mm"
include "eqtrd.mm"
include "3ad2ant2.mm"
include "word.mm"
include "eloni.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "f1f.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "3adant3.mm"
include "fvresd.mm"
include "adantrl.mm"
include "ordsucss.mm"
include "ad2antrr.mm"
include "sylbid.mm"
include "iunss.mm"
include "syl6ibr.mm"
include "3impia.mm"
include "wo.mm"
include "wb.mm"
include "onelon.mm"
include "ex.mm"
include "suceloni.mm"
include "syl6.mm"
include "iunon.mm"
include "mpan.mm"
include "simp1.mm"
include "onsseleq.mm"
include "syl2anc.mm"
include "idd.mm"
include "simpll.mm"
include "wn.mm"
include "simprr.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "ralbidva.mm"
include "biimpa.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "eleq2.mm"
include "biimpar.mm"
include "3adant1.mm"
include "ffvelrn.mm"
include "eqeltrrd.mm"
include "sylan2.mm"
include "onsssuc.mm"
include "syl2an2r.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "3adant2.mm"
include "mpbird.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "expl.mm"
include "imp.mm"
include "feq1.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "rexbiia.mm"
include "syl6bb.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "cfflb.mm"
include "syl21anc.mm"
include "ontri1.mm"
include "mpbid.mm"
include "pm2.21dd.mm"
include "expcomd.mm"
include "com12.mm"
include "3impib.mm"
include "jaod.mm"
include "mpd.mm"
include "3adant1l.mm"
include "ordunel.mm"
include "eqeltrd.mm"
include "3expia.mm"
include "3impa.mm"
include "syldc.mm"
include "a1i.mm"
include "tfis2.mm"
include "mpcom.mm"
include "ralrimiv.mm"
include "onssi.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "mpbiran.mm"
include "onordi.mm"
include "sucid.mm"
include "eliuni.mm"
include "syl6eleqr.mm"
include "mpan2.mm"
include "elun2.mm"
include "eleqtrrd.mm"
include "3eltr4d.mm"
include "expcom.mm"
include "rgen.mm"
include "issmo2.mm"
include "mp3an23.mm"
include "sylc.mm"
include "sseq12d.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "vtoclga.mm"
include "sstr.mm"
include "reximia.mm"
include "ralimi.mm"
include "ad2antlr.mm"
include "fnex.mm"
include "smoeq.mm"
include "3anbi123d.mm"
include "exlimdv.mm"

theorem cfsmolem
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume cfsmolem.2: |- F = ( z e. _V |-> ( ( g ` dom z ) u. U_ t e. dom z suc ( z ` t ) ) )
  assume cfsmolem.3: |- G = ( recs ( F ) |` ( cf ` A ) )

  disjoint f g
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint g t
  disjoint g w
  disjoint g z
  disjoint A g
  disjoint t w
  disjoint t z
  disjoint A t
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint F f
  disjoint F t
  disjoint F z
  disjoint G f
  disjoint G w
  disjoint G z
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint t x
  disjoint t y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( A e. On -> E. f ( f : ( cf ` A ) --> A /\ Smo f /\ A. z e. A E. w e. ( cf ` A ) z C_ ( f ` w ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    cA
    vg
    cv
    #
    wf1
    #
    vz
    cv
    #
    vw
    cv
    #
    @2
    cfv
    #
    wss
    #
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    vg
    wex
    @1
    cA
    vf
    cv
    #
    wf
    #
    @11
    wsmo
    #
    @4
    @5
    @11
    cfv
    #
    wss
    #
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    w3a
    #
    vf
    wex
    #
    vz
    vw
    cA
    vg
    cff1
    @0
    @10
    @19
    vg
    @10
    @0
    @19
    @10
    @0
    wa
    @1
    cA
    cG
    wf
    #
    cG
    wsmo
    #
    @4
    @5
    cG
    cfv
    #
    wss
    #
    vw
    @1
    wrex
    #
    vz
    cA
    wral
    #
    @19
    @3
    @0
    @20
    @9
    @3
    @0
    wa
    #
    vx
    cv
    #
    cG
    cfv
    #
    cA
    wcel
    #
    vx
    @1
    wral
    #
    @20
    @26
    @29
    vx
    @1
    @3
    @0
    @27
    @1
    wcel
    #
    @29
    @27
    con0
    wcel
    #
    @3
    @0
    @31
    w3a
    #
    @29
    @31
    @3
    @32
    @0
    @1
    @27
    cA
    cfon
    #
    oneli
    #
    3ad2ant3
    @33
    @29
    wi
    #
    @3
    @0
    vy
    cv
    #
    @1
    wcel
    #
    w3a
    #
    @37
    cG
    cfv
    #
    cA
    wcel
    #
    wi
    #
    vx
    vy
    vx
    vy
    weq
    #
    @33
    @39
    @29
    @41
    @43
    @31
    @38
    @3
    @0
    @27
    @37
    @1
    eleq1
    3anbi3d
    @43
    @28
    @40
    cA
    @27
    @37
    cG
    fveq2
    eleq1d
    imbi12d
    @42
    vy
    @27
    wral
    #
    @36
    wi
    @32
    @33
    @44
    @41
    vy
    @27
    wral
    #
    @29
    @33
    @42
    @41
    vy
    @27
    @33
    vy
    vx
    wel
    #
    wa
    @3
    @0
    @38
    @42
    @41
    wi
    @3
    @0
    @31
    @46
    simpl1
    @3
    @0
    @31
    @46
    simpl2
    @31
    @3
    @46
    @38
    @0
    @46
    @31
    @38
    @1
    con0
    wcel
    #
    @46
    @31
    wa
    #
    @38
    wi
    @34
    @37
    @27
    @1
    ontr1
    ax-mp
    #
    ancoms
    3ad2antl3
    @39
    @41
    pm2.27
    syl3anc
    ralimdva
    @3
    @0
    @31
    @45
    @29
    wi
    @26
    @31
    @45
    @29
    @26
    @31
    @45
    w3a
    #
    @28
    @27
    @2
    cfv
    #
    vy
    @27
    @37
    cF
    crecs
    #
    cfv
    #
    csuc
    #
    ciun
    #
    cun
    #
    cA
    @31
    @26
    @28
    @56
    wceq
    @45
    @31
    @28
    @27
    @52
    cfv
    #
    @56
    @31
    @28
    @27
    @52
    @1
    cres
    #
    cfv
    @57
    @27
    cG
    @58
    cfsmolem.3
    fveq1i
    @27
    @1
    @52
    fvres
    syl5eq
    #
    @31
    @32
    @57
    @56
    wceq
    #
    @35
    @32
    @57
    @52
    @27
    cres
    #
    cdm
    #
    @2
    cfv
    #
    vt
    @62
    vt
    cv
    #
    @61
    cfv
    #
    csuc
    #
    ciun
    #
    cun
    #
    @56
    @32
    @57
    @61
    cF
    cfv
    #
    @68
    @27
    cF
    recsval
    @61
    cvv
    wcel
    #
    @69
    @68
    wceq
    @52
    wfun
    #
    @27
    cvv
    wcel
    #
    @70
    @52
    con0
    wfn
    #
    @71
    cF
    recsfnon
    #
    con0
    @52
    fnfun
    ax-mp
    vx
    vex
    #
    @52
    @27
    cvv
    resfunexg
    mp2an
    #
    vz
    @61
    @4
    cdm
    #
    @2
    cfv
    #
    vt
    @77
    @64
    @4
    cfv
    #
    csuc
    #
    ciun
    #
    cun
    @68
    cvv
    cF
    @4
    @61
    wceq
    #
    @78
    @63
    @81
    @67
    @82
    @77
    @62
    @2
    @4
    @61
    dmeq
    #
    fveq2d
    @82
    vt
    @77
    @62
    @80
    @66
    @83
    @82
    @79
    @65
    wceq
    @80
    @66
    wceq
    @64
    @4
    @61
    fveq1
    @79
    @65
    suceq
    syl
    iuneq12d
    uneq12d
    cfsmolem.2
    @63
    @67
    @62
    @2
    fvex
    vt
    @62
    @66
    @61
    @76
    dmex
    @65
    @64
    @61
    fvex
    sucex
    iunex
    unex
    fvmpt
    ax-mp
    syl6eq
    @32
    @61
    @27
    wfn
    #
    @62
    @27
    wceq
    #
    @68
    @56
    wceq
    @32
    @73
    @27
    con0
    wss
    @84
    @74
    @27
    onss
    con0
    @27
    @52
    fnssres
    sylancr
    #
    @27
    @61
    fndm
    @85
    @63
    @51
    @67
    @55
    @62
    @27
    @2
    fveq2
    @85
    @67
    vt
    @27
    @66
    ciun
    #
    @55
    vt
    @62
    @27
    @66
    iuneq1
    @87
    vt
    @27
    @64
    @52
    cfv
    #
    csuc
    #
    ciun
    #
    @55
    vt
    @27
    @66
    @89
    vt
    vx
    wel
    @65
    @88
    wceq
    @66
    @89
    wceq
    @64
    @27
    @52
    fvres
    @65
    @88
    suceq
    syl
    iuneq2i
    vy
    vt
    @27
    @54
    @89
    vy
    vt
    weq
    @53
    @88
    wceq
    @54
    @89
    wceq
    @37
    @64
    @52
    fveq2
    @53
    @88
    suceq
    syl
    cbviunv
    #
    eqtr4i
    syl6eq
    uneq12d
    3syl
    eqtrd
    #
    syl
    eqtrd
    #
    3ad2ant2
    @50
    cA
    word
    #
    @51
    cA
    wcel
    #
    @55
    cA
    wcel
    #
    @56
    cA
    wcel
    @26
    @31
    @94
    @45
    @0
    @94
    @3
    cA
    eloni
    #
    adantl
    3ad2ant1
    @26
    @31
    @95
    @45
    @3
    @31
    @95
    @0
    @3
    @1
    cA
    @27
    @2
    @1
    cA
    @2
    f1f
    ffvelrnda
    adantlr
    3adant3
    @0
    @31
    @45
    @96
    @3
    @0
    @31
    @45
    w3a
    #
    @55
    cA
    wss
    #
    @96
    @0
    @31
    @45
    @99
    @0
    @31
    wa
    #
    @45
    @54
    cA
    wss
    #
    vy
    @27
    wral
    @99
    @100
    @41
    @101
    vy
    @27
    @100
    @46
    wa
    #
    @41
    @53
    cA
    wcel
    #
    @101
    @102
    @40
    @53
    cA
    @46
    @100
    @40
    @53
    wceq
    #
    @46
    @31
    @104
    @0
    @48
    @40
    @37
    @58
    cfv
    @53
    @37
    cG
    @58
    cfsmolem.3
    fveq1i
    @48
    @37
    @1
    @52
    @49
    fvresd
    syl5eq
    #
    adantrl
    ancoms
    eleq1d
    #
    @0
    @103
    @101
    wi
    #
    @31
    @46
    @0
    @94
    @107
    @97
    @53
    cA
    ordsucss
    syl
    ad2antrr
    sylbid
    ralimdva
    vy
    @27
    @54
    cA
    iunss
    syl6ibr
    3impia
    @98
    @99
    @96
    @55
    cA
    wceq
    #
    wo
    #
    @96
    @98
    @55
    con0
    wcel
    #
    @0
    @99
    @109
    wb
    @98
    @54
    con0
    wcel
    #
    vy
    @27
    wral
    #
    @110
    @0
    @31
    @45
    @112
    @100
    @41
    @111
    vy
    @27
    @102
    @41
    @53
    con0
    wcel
    #
    @111
    @102
    @41
    @103
    @113
    @106
    @0
    @103
    @113
    wi
    @31
    @46
    @0
    @103
    @113
    cA
    @53
    onelon
    #
    ex
    ad2antrr
    sylbid
    @53
    suceloni
    syl6
    ralimdva
    3impia
    @72
    @112
    @110
    @75
    vy
    @27
    @54
    cvv
    iunon
    mpan
    syl
    @0
    @31
    @45
    simp1
    @55
    cA
    onsseleq
    syl2anc
    @98
    @96
    @96
    @108
    @98
    @96
    idd
    @0
    @31
    @45
    @108
    @96
    wi
    #
    @31
    @45
    wa
    #
    @0
    @115
    @116
    @108
    @0
    @96
    @116
    @108
    @0
    wa
    #
    @96
    @116
    @117
    wa
    #
    @31
    @96
    @31
    @45
    @117
    simpll
    @118
    @1
    @27
    wss
    #
    @31
    wn
    #
    @118
    @0
    @32
    @27
    cA
    @11
    wf
    #
    @64
    @37
    @11
    cfv
    #
    wss
    #
    vy
    @27
    wrex
    #
    vt
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    @119
    @116
    @108
    @0
    simprr
    @31
    @32
    @45
    @117
    @35
    ad2antrr
    @116
    @27
    cA
    @61
    wf
    #
    @117
    @64
    @53
    wss
    #
    vy
    @27
    wrex
    #
    vt
    cA
    wral
    #
    @127
    @116
    @84
    @37
    @61
    cfv
    #
    cA
    wcel
    #
    vy
    @27
    wral
    #
    @128
    @31
    @84
    @45
    @31
    @32
    @84
    @35
    @86
    syl
    adantr
    @31
    @45
    @134
    @31
    @41
    @133
    vy
    @27
    @31
    @46
    wa
    #
    @40
    @132
    cA
    @135
    @40
    @53
    @132
    @46
    @31
    @104
    @105
    ancoms
    @46
    @132
    @53
    wceq
    #
    @31
    @37
    @27
    @52
    fvres
    #
    adantl
    eqtr4d
    eleq1d
    ralbidva
    biimpa
    vy
    @27
    cA
    @61
    ffnfv
    sylanbrc
    #
    @116
    @117
    @131
    @116
    @128
    @117
    @131
    wi
    @138
    @128
    @108
    @0
    @131
    @128
    @108
    wa
    #
    @0
    wa
    @130
    vt
    cA
    @139
    @0
    @64
    cA
    wcel
    #
    @130
    @128
    @108
    @0
    @140
    wa
    #
    @130
    @128
    @108
    @141
    w3a
    @130
    @64
    @55
    wcel
    #
    @108
    @141
    @142
    @128
    @108
    @140
    @142
    @0
    @108
    @142
    @140
    @55
    cA
    @64
    eleq2
    biimpar
    adantrl
    3adant1
    @128
    @141
    @130
    @142
    wb
    #
    @108
    @141
    @128
    @143
    @141
    @128
    wa
    #
    @130
    @64
    @54
    wcel
    #
    vy
    @27
    wrex
    @142
    @144
    @129
    @145
    vy
    @27
    @141
    @128
    @46
    @129
    @145
    wb
    #
    @141
    @64
    con0
    wcel
    @128
    @46
    wa
    #
    @113
    @146
    cA
    @64
    onelon
    @0
    @147
    @113
    @140
    @147
    @0
    @103
    @113
    @147
    @132
    @53
    cA
    @46
    @136
    @128
    @137
    adantl
    @27
    cA
    @37
    @61
    ffvelrn
    eqeltrrd
    @114
    sylan2
    adantlr
    @64
    @53
    onsssuc
    syl2an2r
    anassrs
    rexbidva
    vy
    @64
    @27
    @54
    eliun
    syl6bbr
    ancoms
    3adant2
    mpbird
    3expa
    anassrs
    ralrimiva
    expl
    syl
    imp
    @126
    @128
    @131
    wa
    vf
    @61
    @76
    @11
    @61
    wceq
    #
    @121
    @128
    @125
    @131
    @27
    cA
    @11
    @61
    feq1
    @148
    @124
    @130
    vt
    cA
    @148
    @124
    @64
    @132
    wss
    #
    vy
    @27
    wrex
    @130
    @148
    @123
    @149
    vy
    @27
    @148
    @122
    @132
    @64
    @37
    @11
    @61
    fveq1
    sseq2d
    rexbidv
    @149
    @129
    vy
    @27
    @46
    @132
    @53
    @64
    @137
    sseq2d
    rexbiia
    syl6bb
    ralbidv
    anbi12d
    spcev
    syl2an2r
    @0
    @32
    wa
    @127
    @119
    vt
    vy
    cA
    @27
    vf
    cfflb
    imp
    syl21anc
    @31
    @119
    @120
    wb
    #
    @45
    @117
    @31
    @47
    @32
    @150
    @34
    @35
    @1
    @27
    ontri1
    sylancr
    ad2antrr
    mpbid
    pm2.21dd
    ex
    expcomd
    com12
    3impib
    jaod
    sylbid
    mpd
    3adant1l
    cA
    @51
    @55
    ordunel
    syl3anc
    eqeltrd
    3expia
    3impa
    syldc
    a1i
    tfis2
    mpcom
    3expia
    ralrimiv
    @20
    cG
    @1
    wfn
    #
    @30
    @73
    @1
    con0
    wss
    #
    @151
    @74
    @1
    @34
    onssi
    @73
    @152
    wa
    @58
    @1
    wfn
    @151
    con0
    @1
    @52
    fnssres
    @1
    cG
    @58
    cfsmolem.3
    fneq1i
    sylibr
    mp2an
    #
    vx
    @1
    cA
    cG
    ffnfv
    mpbiran
    sylibr
    #
    adantlr
    @3
    @0
    @21
    @9
    @26
    cA
    con0
    wss
    #
    @20
    @21
    @0
    @155
    @3
    cA
    onss
    adantl
    @154
    @155
    @1
    word
    #
    @40
    @28
    wcel
    #
    vy
    @27
    wral
    #
    vx
    @1
    wral
    #
    @20
    @21
    wi
    @1
    @34
    onordi
    @158
    vx
    @1
    @31
    @157
    vy
    @27
    @46
    @31
    @157
    @48
    @53
    @57
    @40
    @28
    @48
    @53
    @56
    @57
    @46
    @53
    @56
    wcel
    #
    @31
    @46
    @53
    @55
    wcel
    #
    @160
    @46
    @53
    @54
    wcel
    #
    @161
    @53
    @37
    @52
    fvex
    sucid
    @46
    @162
    wa
    @53
    @90
    @55
    vt
    @37
    @89
    @54
    @27
    @53
    vt
    vy
    weq
    @88
    @53
    wceq
    @89
    @54
    wceq
    @64
    @37
    @52
    fveq2
    @88
    @53
    suceq
    syl
    eliuni
    @91
    syl6eleqr
    mpan2
    @53
    @55
    @51
    elun2
    syl
    adantr
    @48
    @32
    @60
    @31
    @32
    @46
    @35
    adantl
    @92
    syl
    eleqtrrd
    @105
    @31
    @28
    @57
    wceq
    @46
    @59
    adantl
    3eltr4d
    expcom
    ralrimiv
    rgen
    @20
    @155
    @156
    @159
    w3a
    @21
    vx
    vy
    @1
    cA
    cG
    issmo2
    com12
    mp3an23
    sylc
    adantlr
    @9
    @25
    @3
    @0
    @8
    @24
    vz
    cA
    @7
    @23
    vw
    @1
    @5
    @1
    wcel
    @6
    @22
    wss
    #
    @7
    @23
    wi
    @51
    @28
    wss
    @163
    vx
    @5
    @1
    vx
    vw
    weq
    @51
    @6
    @28
    @22
    @27
    @5
    @2
    fveq2
    @27
    @5
    cG
    fveq2
    sseq12d
    @31
    @56
    @51
    @28
    @51
    @55
    ssun1
    @93
    syl5sseqr
    vtoclga
    @7
    @163
    @23
    @4
    @6
    @22
    sstr
    expcom
    syl
    reximia
    ralimi
    ad2antlr
    @18
    @20
    @21
    @25
    w3a
    vf
    cG
    @151
    @47
    cG
    cvv
    wcel
    @153
    @34
    @1
    con0
    cG
    fnex
    mp2an
    @11
    cG
    wceq
    #
    @12
    @20
    @13
    @21
    @17
    @25
    @1
    cA
    @11
    cG
    feq1
    @11
    cG
    smoeq
    @164
    @16
    @24
    vz
    cA
    @164
    @15
    @23
    vw
    @1
    @164
    @14
    @22
    @4
    @5
    @11
    cG
    fveq1
    sseq2d
    rexbidv
    ralbidv
    3anbi123d
    spcev
    syl3anc
    expcom
    exlimdv
    mpd
end
