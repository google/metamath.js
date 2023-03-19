include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wwe.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "ccnv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "wrex.mm"
include "copab.mm"
include "wbr.mm"
include "ccnf.mm"
include "co.mm"
include "wf1o.mm"
include "cfsupp.mm"
include "cmap.mm"
include "crab.mm"
include "eqid.mm"
include "cep.mm"
include "wiso.mm"
include "simprr.mm"
include "adantr.mm"
include "oiiso.mm"
include "syl2anc.mm"
include "isof1o.mm"
include "syl.mm"
include "simprl.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "oiexg.mm"
include "ad2antll.mm"
include "dmexg.mm"
include "ad2antrl.mm"
include "c0.mm"
include "wne.mm"
include "crn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "word.mm"
include "wb.mm"
include "oicl.mm"
include "ord0eln0.mm"
include "ax-mp.mm"
include "oif.mm"
include "ffvelrni.mm"
include "syl5eqel.mm"
include "mapfien.mm"
include "con0.mm"
include "oion.mm"
include "cantnfdm.mm"
include "fveq2i.mm"
include "f1ocnvfv1.mm"
include "syl5eq.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eqtr4d.mm"
include "f1oeq3.mm"
include "mpbird.mm"
include "coi.mm"
include "coe.mm"
include "oemapwe.mm"
include "simpld.mm"
include "f1owe.mm"
include "sylc.mm"
include "weinxp.mm"
include "sylib.mm"
include "wfn.mm"
include "f1ofn.mm"
include "fveq2.mm"
include "breq12d.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexrn.mm"
include "rexeqdv.mm"
include "cnvexg.mm"
include "vex.mm"
include "coexg.mm"
include "sylancr.mm"
include "fveq1.mm"
include "eleq12.mm"
include "syl2an.mm"
include "eqeqan12d.mm"
include "imbi2d.mm"
include "rexbidv.mm"
include "brabga.mm"
include "weq.mm"
include "coeq1.mm"
include "coeq2d.mm"
include "fvmptg.mm"
include "ad2antrr.mm"
include "isocnv.mm"
include "wf.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "isorel.mm"
include "syl12anc.mm"
include "fvex.mm"
include "epelc.mm"
include "syl6bb.mm"
include "fco.mm"
include "sylancl.mm"
include "fvco3.mm"
include "sylancom.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq12d.mm"
include "bitr4d.mm"
include "raleqdv.mm"
include "breq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "ralrn.mm"
include "bitr3d.mm"
include "epel.mm"
include "syl5bbr.mm"
include "adantrr.mm"
include "wf1.mm"
include "f1of1.mm"
include "ffvelrnd.mm"
include "f1fveq.mm"
include "3bitrd.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "3bitr4rd.mm"
include "3bitr3d.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "opabbidv.mm"
include "df-xp.mm"
include "ineq12i.mm"
include "inopab.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "3eqtr4g.mm"
include "weeq1.mm"
include "wn.mm"
include "we0.mm"
include "elmapex.mm"
include "con3i.mm"
include "pm2.21d.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "weeq2.mm"
include "mpbiri.mm"
include "pm2.61d1.mm"

theorem wemapwe
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  assume wemapwe.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( z R w -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemapwe.u: |- U = { x e. ( B ^m A ) | x finSupp Z }
  assume wemapwe.2: |- ( ph -> R We A )
  assume wemapwe.3: |- ( ph -> S We B )
  assume wemapwe.4: |- ( ph -> B =/= (/) )
  assume wemapwe.5: |- F = OrdIso ( R , A )
  assume wemapwe.6: |- G = OrdIso ( S , B )
  assume wemapwe.7: |- Z = ( G ` (/) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint R w
  disjoint R z
  disjoint S z
  disjoint U x
  disjoint U y
  disjoint Z x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c d
  disjoint c f
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint d f
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B f
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F f
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G f
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint f ph
  disjoint R c
  disjoint R d
  disjoint S c
  disjoint U c
  disjoint U d
  disjoint U f
  disjoint Z f
  assert |- ( ph -> T We U )

  proof
    wph
    cB
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    wa
    #
    cU
    cT
    wwe
    #
    wph
    @2
    @3
    wph
    @2
    wa
    #
    cU
    cT
    cU
    cU
    cxp
    #
    cin
    #
    wwe
    #
    @3
    @4
    @7
    cU
    vx
    cv
    #
    vf
    cU
    cG
    ccnv
    #
    vf
    cv
    #
    cF
    ccom
    #
    ccom
    #
    cmpt
    #
    cfv
    #
    vy
    cv
    #
    @13
    cfv
    #
    vc
    cv
    #
    va
    cv
    #
    cfv
    #
    @17
    vb
    cv
    #
    cfv
    #
    wcel
    #
    @17
    vd
    cv
    #
    wcel
    #
    @23
    @18
    cfv
    #
    @23
    @20
    cfv
    #
    wceq
    #
    wi
    #
    vd
    cF
    cdm
    #
    wral
    #
    wa
    #
    vc
    @29
    wrex
    #
    va
    vb
    copab
    #
    wbr
    #
    vx
    vy
    copab
    #
    @5
    cin
    #
    wwe
    #
    @4
    cU
    @35
    wwe
    #
    @37
    @4
    cU
    cG
    cdm
    #
    @29
    ccnf
    co
    cdm
    #
    @13
    wf1o
    #
    @40
    @33
    wwe
    #
    @38
    @4
    @41
    cU
    @8
    cZ
    @9
    cfv
    #
    cfsupp
    wbr
    #
    vx
    @39
    @29
    cmap
    co
    #
    crab
    #
    @13
    wf1o
    #
    @4
    vx
    cA
    cB
    @29
    @39
    cU
    @46
    vf
    cF
    @9
    @43
    cZ
    wemapwe.u
    @46
    eqid
    @43
    eqid
    @4
    @29
    cA
    cep
    cR
    cF
    wiso
    #
    @29
    cA
    cF
    wf1o
    #
    @4
    @1
    cA
    cR
    wwe
    #
    @48
    wph
    @0
    @1
    simprr
    #
    wph
    @50
    @2
    wemapwe.2
    adantr
    cA
    cR
    cF
    cvv
    wemapwe.5
    oiiso
    syl2anc
    #
    @29
    cA
    cep
    cR
    cF
    isof1o
    syl
    #
    @4
    @39
    cB
    cep
    cS
    cG
    wiso
    #
    @39
    cB
    cG
    wf1o
    #
    cB
    @39
    @9
    wf1o
    #
    @4
    @0
    cB
    cS
    wwe
    #
    @54
    wph
    @0
    @1
    simprl
    #
    wph
    @57
    @2
    wemapwe.3
    adantr
    cB
    cS
    cG
    cvv
    wemapwe.6
    oiiso
    syl2anc
    #
    @39
    cB
    cep
    cS
    cG
    isof1o
    #
    @39
    cB
    cG
    f1ocnv
    #
    3syl
    @51
    @58
    @4
    cF
    cvv
    wcel
    #
    @29
    cvv
    wcel
    @1
    @62
    wph
    @0
    cA
    cR
    cF
    cvv
    wemapwe.5
    oiexg
    ad2antll
    #
    cF
    cvv
    dmexg
    syl
    @4
    cG
    cvv
    wcel
    #
    @39
    cvv
    wcel
    @0
    @64
    wph
    @1
    cB
    cS
    cG
    cvv
    wemapwe.6
    oiexg
    ad2antrl
    #
    cG
    cvv
    dmexg
    syl
    @4
    cZ
    c0
    cG
    cfv
    #
    cB
    wemapwe.7
    @4
    c0
    @39
    wcel
    #
    @66
    cB
    wcel
    @4
    @39
    c0
    wne
    #
    @67
    @4
    cG
    crn
    #
    c0
    wne
    @68
    @4
    @69
    cB
    c0
    @4
    @55
    @39
    cB
    cG
    wfo
    @69
    cB
    wceq
    @4
    @54
    @55
    @59
    @60
    syl
    #
    @39
    cB
    cG
    f1ofo
    @39
    cB
    cG
    forn
    3syl
    wph
    cB
    c0
    wne
    @2
    wemapwe.4
    adantr
    eqnetrd
    @39
    c0
    @69
    c0
    cG
    dm0rn0
    necon3bii
    sylibr
    @39
    word
    @67
    @68
    wb
    cB
    cS
    cG
    wemapwe.6
    oicl
    @39
    ord0eln0
    ax-mp
    sylibr
    #
    @39
    cB
    c0
    cG
    cB
    cS
    cG
    wemapwe.6
    oif
    ffvelrni
    syl
    syl5eqel
    mapfien
    @4
    @40
    @46
    wceq
    @41
    @47
    wb
    @4
    @40
    @8
    c0
    cfsupp
    wbr
    #
    vx
    @45
    crab
    #
    @46
    @4
    @39
    @29
    @73
    vx
    @73
    eqid
    @0
    @39
    con0
    wcel
    wph
    @1
    cB
    cS
    cG
    cvv
    wemapwe.6
    oion
    ad2antrl
    #
    @1
    @29
    con0
    wcel
    wph
    @0
    cA
    cR
    cF
    cvv
    wemapwe.5
    oion
    ad2antll
    #
    cantnfdm
    @4
    @44
    @72
    vx
    @45
    @4
    @43
    c0
    @8
    cfsupp
    @4
    @43
    @66
    @9
    cfv
    #
    c0
    cZ
    @66
    @9
    wemapwe.7
    fveq2i
    @4
    @55
    @67
    @76
    c0
    wceq
    @70
    @71
    @39
    cB
    c0
    cG
    f1ocnvfv1
    syl2anc
    syl5eq
    breq2d
    rabbidv
    eqtr4d
    @40
    @46
    cU
    @13
    f1oeq3
    syl
    mpbird
    @4
    @42
    @40
    @33
    coi
    cdm
    @39
    @29
    coe
    co
    wceq
    @4
    va
    vb
    vc
    vd
    @39
    @29
    @40
    @33
    @40
    eqid
    @74
    @75
    @33
    eqid
    #
    oemapwe
    simpld
    vx
    vy
    cU
    @40
    @35
    @33
    @13
    @35
    eqid
    f1owe
    sylc
    cU
    @35
    weinxp
    sylib
    @4
    @6
    @36
    wceq
    @7
    @37
    wb
    @4
    vz
    cv
    #
    @8
    cfv
    #
    @78
    @15
    cfv
    #
    cS
    wbr
    #
    @78
    vw
    cv
    #
    cR
    wbr
    #
    @82
    @8
    cfv
    #
    @82
    @15
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    #
    @8
    cU
    wcel
    #
    @15
    cU
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    @34
    @93
    wa
    #
    vx
    vy
    copab
    #
    @6
    @36
    @4
    @94
    @96
    vx
    vy
    @4
    @93
    @90
    @34
    @4
    @93
    @90
    @34
    wb
    @4
    @93
    wa
    #
    @89
    vz
    cF
    crn
    #
    wrex
    #
    @17
    cF
    cfv
    #
    @8
    cfv
    #
    @101
    @15
    cfv
    #
    cS
    wbr
    #
    @101
    @82
    cR
    wbr
    #
    @86
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vc
    @29
    wrex
    #
    @90
    @34
    @98
    @49
    cF
    @29
    wfn
    #
    @100
    @109
    wb
    @4
    @49
    @93
    @53
    adantr
    #
    @29
    cA
    cF
    f1ofn
    #
    @89
    @108
    vz
    vc
    @29
    cF
    @78
    @101
    wceq
    #
    @81
    @104
    @88
    @107
    @113
    @79
    @102
    @80
    @103
    cS
    @78
    @101
    @8
    fveq2
    @78
    @101
    @15
    fveq2
    breq12d
    @113
    @87
    @106
    vw
    cA
    @113
    @83
    @105
    @86
    @78
    @101
    @82
    cR
    breq1
    imbi1d
    ralbidv
    anbi12d
    rexrn
    3syl
    @98
    @89
    vz
    @99
    cA
    @98
    @49
    @29
    cA
    cF
    wfo
    @99
    cA
    wceq
    @111
    @29
    cA
    cF
    f1ofo
    @29
    cA
    cF
    forn
    3syl
    #
    rexeqdv
    @98
    @9
    @8
    cF
    ccom
    #
    ccom
    #
    @9
    @15
    cF
    ccom
    #
    ccom
    #
    @33
    wbr
    #
    @17
    @116
    cfv
    #
    @17
    @118
    cfv
    #
    wcel
    #
    @24
    @23
    @116
    cfv
    #
    @23
    @118
    cfv
    #
    wceq
    #
    wi
    #
    vd
    @29
    wral
    #
    wa
    #
    vc
    @29
    wrex
    #
    @34
    @109
    @98
    @116
    cvv
    wcel
    #
    @118
    cvv
    wcel
    #
    @119
    @129
    wb
    @98
    @9
    cvv
    wcel
    #
    @115
    cvv
    wcel
    #
    @130
    @98
    @64
    @132
    @4
    @64
    @93
    @65
    adantr
    cG
    cvv
    cnvexg
    syl
    #
    @98
    @8
    cvv
    wcel
    @62
    @133
    vx
    vex
    @4
    @62
    @93
    @63
    adantr
    #
    @8
    cF
    cvv
    cvv
    coexg
    sylancr
    @9
    @115
    cvv
    cvv
    coexg
    syl2anc
    #
    @98
    @132
    @117
    cvv
    wcel
    #
    @131
    @134
    @98
    @15
    cvv
    wcel
    @62
    @137
    vy
    vex
    @135
    @15
    cF
    cvv
    cvv
    coexg
    sylancr
    @9
    @117
    cvv
    cvv
    coexg
    syl2anc
    #
    @32
    @129
    va
    vb
    @116
    @118
    @33
    cvv
    cvv
    @18
    @116
    wceq
    #
    @20
    @118
    wceq
    #
    wa
    #
    @31
    @128
    vc
    @29
    @141
    @22
    @122
    @30
    @127
    @139
    @19
    @120
    wceq
    @21
    @121
    wceq
    @22
    @122
    wb
    @140
    @17
    @18
    @116
    fveq1
    @17
    @20
    @118
    fveq1
    @19
    @120
    @21
    @121
    eleq12
    syl2an
    @141
    @28
    @126
    vd
    @29
    @141
    @27
    @125
    @24
    @139
    @140
    @25
    @123
    @26
    @124
    @23
    @18
    @116
    fveq1
    @23
    @20
    @118
    fveq1
    eqeqan12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    @77
    brabga
    syl2anc
    @98
    @14
    @116
    @16
    @118
    @33
    @98
    @91
    @130
    @14
    @116
    wceq
    @4
    @91
    @92
    simprl
    #
    @136
    vf
    @8
    @12
    @116
    cU
    cvv
    @13
    vf
    vx
    weq
    @11
    @115
    @9
    @10
    @8
    cF
    coeq1
    coeq2d
    @13
    eqid
    #
    fvmptg
    syl2anc
    @98
    @92
    @131
    @16
    @118
    wceq
    @4
    @91
    @92
    simprr
    #
    @138
    vf
    @15
    @12
    @118
    cU
    cvv
    @13
    vf
    vy
    weq
    @11
    @117
    @9
    @10
    @15
    cF
    coeq1
    coeq2d
    @143
    fvmptg
    syl2anc
    breq12d
    @98
    @108
    @128
    vc
    @29
    @98
    @17
    @29
    wcel
    #
    wa
    #
    @104
    @122
    @107
    @127
    @146
    @104
    @102
    @9
    cfv
    #
    @103
    @9
    cfv
    #
    wcel
    #
    @122
    @146
    @104
    @147
    @148
    cep
    wbr
    #
    @149
    @146
    cB
    @39
    cS
    cep
    @9
    wiso
    #
    @102
    cB
    wcel
    #
    @103
    cB
    wcel
    #
    @104
    @150
    wb
    @146
    @54
    @151
    @4
    @54
    @93
    @145
    @59
    ad2antrr
    @39
    cB
    cep
    cS
    cG
    isocnv
    syl
    @98
    cA
    cB
    @8
    wf
    #
    @101
    cA
    wcel
    #
    @152
    @145
    @98
    @8
    cB
    cA
    cmap
    co
    #
    wcel
    #
    @154
    @98
    cU
    @156
    @8
    cU
    @8
    cZ
    cfsupp
    wbr
    #
    vx
    @156
    crab
    #
    @156
    wemapwe.u
    @158
    vx
    @156
    ssrab2
    eqsstri
    #
    @142
    sseldi
    @8
    cB
    cA
    elmapi
    syl
    #
    @29
    cA
    @17
    cF
    cA
    cR
    cF
    wemapwe.5
    oif
    #
    ffvelrni
    #
    cA
    cB
    @101
    @8
    ffvelrn
    syl2an
    @98
    cA
    cB
    @15
    wf
    #
    @155
    @153
    @145
    @98
    @15
    @156
    wcel
    @164
    @98
    cU
    @156
    @15
    @160
    @144
    sseldi
    @15
    cB
    cA
    elmapi
    syl
    #
    @163
    cA
    cB
    @101
    @15
    ffvelrn
    syl2an
    cB
    @39
    @102
    @103
    cS
    cep
    @9
    isorel
    syl12anc
    @147
    @148
    @103
    @9
    fvex
    epelc
    syl6bb
    @146
    @120
    @147
    @121
    @148
    @146
    @120
    @17
    @115
    cfv
    #
    @9
    cfv
    #
    @147
    @98
    @145
    @29
    cB
    @115
    wf
    #
    @120
    @167
    wceq
    @146
    @154
    @29
    cA
    cF
    wf
    #
    @168
    @98
    @154
    @145
    @161
    adantr
    @162
    @29
    cA
    cB
    @8
    cF
    fco
    sylancl
    #
    @29
    cB
    @17
    @9
    @115
    fvco3
    sylancom
    @146
    @166
    @102
    @9
    @146
    @169
    @145
    @166
    @102
    wceq
    @162
    @98
    @145
    simpr
    #
    @29
    cA
    @17
    @8
    cF
    fvco3
    sylancr
    fveq2d
    eqtrd
    @146
    @121
    @17
    @117
    cfv
    #
    @9
    cfv
    #
    @148
    @98
    @145
    @29
    cB
    @117
    wf
    #
    @121
    @173
    wceq
    @146
    @164
    @169
    @174
    @98
    @164
    @145
    @165
    adantr
    @162
    @29
    cA
    cB
    @15
    cF
    fco
    sylancl
    #
    @29
    cB
    @17
    @9
    @117
    fvco3
    sylancom
    @146
    @172
    @103
    @9
    @146
    @169
    @145
    @172
    @103
    wceq
    @162
    @171
    @29
    cA
    @17
    @15
    cF
    fvco3
    sylancr
    fveq2d
    eqtrd
    eleq12d
    bitr4d
    @146
    @107
    @101
    @23
    cF
    cfv
    #
    cR
    wbr
    #
    @176
    @8
    cfv
    #
    @176
    @15
    cfv
    #
    wceq
    #
    wi
    #
    vd
    @29
    wral
    #
    @127
    @98
    @107
    @182
    wb
    @145
    @98
    @106
    vw
    @99
    wral
    #
    @107
    @182
    @98
    @106
    vw
    @99
    cA
    @114
    raleqdv
    @98
    @49
    @110
    @183
    @182
    wb
    @111
    @112
    @106
    @181
    vw
    vd
    @29
    cF
    @82
    @176
    wceq
    #
    @105
    @177
    @86
    @180
    @82
    @176
    @101
    cR
    breq2
    @184
    @84
    @178
    @85
    @179
    @82
    @176
    @8
    fveq2
    @82
    @176
    @15
    fveq2
    eqeq12d
    imbi12d
    ralrn
    3syl
    bitr3d
    adantr
    @146
    @126
    @181
    vd
    @29
    @98
    @145
    @23
    @29
    wcel
    #
    @126
    @181
    wb
    @98
    @145
    @185
    wa
    #
    wa
    #
    @24
    @177
    @125
    @180
    @24
    @17
    @23
    cep
    wbr
    #
    @187
    @177
    vc
    vd
    epel
    @98
    @186
    @48
    @188
    @177
    wb
    @4
    @48
    @93
    @186
    @52
    ad2antrr
    @29
    cA
    @17
    @23
    cep
    cR
    cF
    isorel
    sylancom
    syl5bbr
    @187
    @125
    @23
    @115
    cfv
    #
    @9
    cfv
    #
    @23
    @117
    cfv
    #
    @9
    cfv
    #
    wceq
    #
    @189
    @191
    wceq
    #
    @180
    @187
    @123
    @190
    @124
    @192
    @187
    @168
    @185
    @123
    @190
    wceq
    @98
    @145
    @168
    @185
    @170
    adantrr
    #
    @98
    @145
    @185
    simprr
    #
    @29
    cB
    @23
    @9
    @115
    fvco3
    syl2anc
    @187
    @174
    @185
    @124
    @192
    wceq
    @98
    @145
    @174
    @185
    @175
    adantrr
    #
    @196
    @29
    cB
    @23
    @9
    @117
    fvco3
    syl2anc
    eqeq12d
    @187
    cB
    @39
    @9
    wf1
    #
    @189
    cB
    wcel
    @191
    cB
    wcel
    @193
    @194
    wb
    @187
    @55
    @56
    @198
    @4
    @55
    @93
    @186
    @70
    ad2antrr
    @61
    cB
    @39
    @9
    f1of1
    3syl
    @187
    @29
    cB
    @23
    @115
    @195
    @196
    ffvelrnd
    @187
    @29
    cB
    @23
    @117
    @197
    @196
    ffvelrnd
    cB
    @39
    @189
    @191
    @9
    f1fveq
    syl12anc
    @187
    @189
    @178
    @191
    @179
    @187
    @169
    @185
    @189
    @178
    wceq
    @162
    @196
    @29
    cA
    @23
    @8
    cF
    fvco3
    sylancr
    @187
    @169
    @185
    @191
    @179
    wceq
    @162
    @196
    @29
    cA
    @23
    @15
    cF
    fvco3
    sylancr
    eqeq12d
    3bitrd
    imbi12d
    anassrs
    ralbidva
    bitr4d
    anbi12d
    rexbidva
    3bitr4rd
    3bitr3d
    ex
    pm5.32rd
    opabbidv
    @6
    @90
    vx
    vy
    copab
    #
    @93
    vx
    vy
    copab
    #
    cin
    @95
    cT
    @199
    @5
    @200
    wemapwe.t
    vx
    vy
    cU
    cU
    df-xp
    #
    ineq12i
    @90
    @93
    vx
    vy
    inopab
    eqtri
    @36
    @35
    @200
    cin
    @97
    @5
    @200
    @35
    @201
    ineq2i
    @34
    @93
    vx
    vy
    inopab
    eqtri
    3eqtr4g
    cU
    @6
    @36
    weeq1
    syl
    mpbird
    cU
    cT
    weinxp
    sylibr
    ex
    @2
    wn
    #
    @3
    c0
    cT
    wwe
    #
    cT
    we0
    @202
    cU
    c0
    wceq
    @3
    @203
    wb
    @202
    cU
    @159
    c0
    wemapwe.u
    @202
    @158
    wn
    #
    vx
    @156
    wral
    @159
    c0
    wceq
    @202
    @204
    vx
    @156
    @202
    @157
    @204
    @157
    @2
    @8
    cB
    cA
    elmapex
    con3i
    pm2.21d
    ralrimiv
    @158
    vx
    @156
    rabeq0
    sylibr
    syl5eq
    cU
    c0
    cT
    weeq2
    syl
    mpbiri
    pm2.61d1
end
