include "crn.mm"
include "cuni.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "cv.mm"
include "cin.mm"
include "co.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "wral.mm"
include "cpw.mm"
include "wex.mm"
include "vex.mm"
include "eldm.mm"
include "fpwwe2lem2.mm"
include "simprbda.mm"
include "simpld.mm"
include "selpw.mm"
include "sylibr.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "sspwuni.mm"
include "sylib.mm"
include "syl5eqss.mm"
include "elrn.mm"
include "simprd.mm"
include "relopabi.mm"
include "releldmi.mm"
include "adantl.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "jca.mm"
include "wfr.mm"
include "weq.mm"
include "w3o.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wel.mm"
include "n0.mm"
include "ssel2.mm"
include "eleq2i.mm"
include "eluni2.mm"
include "bitri.mm"
include "cvv.mm"
include "inex2.mm"
include "a1i.mm"
include "simplbda.mm"
include "ad2ant2r.mm"
include "wefr.mm"
include "inss2.mm"
include "simplrr.mm"
include "simprr.mm"
include "inelcm.mm"
include "fri.mm"
include "syl22anc.mm"
include "inss1.mm"
include "simprl.mm"
include "sseldi.mm"
include "ralnex.mm"
include "cop.mm"
include "df-br.mm"
include "simprll.mm"
include "adantr.mm"
include "simp-4l.mm"
include "ad2antrr.mm"
include "simprlr.mm"
include "wb.mm"
include "mpbid.mm"
include "syl12anc.mm"
include "ssbrd.mm"
include "mpd.mm"
include "brxp.mm"
include "simplbi.mm"
include "brinxp2.mm"
include "syl3anbrc.mm"
include "breqd.mm"
include "mpbird.mm"
include "elind.mm"
include "breq1.mm"
include "rspcev.mm"
include "sseldd.mm"
include "syl6eqss.mm"
include "wo.mm"
include "w3a.mm"
include "adantlr.mm"
include "fpwwe2lem10.mm"
include "mpjaodan.mm"
include "expr.mm"
include "syl5bir.mm"
include "rexlimdv.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "reximdv2.mm"
include "exp32.mm"
include "expimpd.mm"
include "alrimiv.mm"
include "df-fr.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "eeanv.mm"
include "wor.mm"
include "weso.mm"
include "simplrl.mm"
include "solin.mm"
include "relelrni.mm"
include "ad2antll.mm"
include "idd.mm"
include "3orim123d.mm"
include "adantrr.mm"
include "ad2antrl.mm"
include "exp31.mm"
include "exlimdvv.mm"
include "rexlimdvv.mm"
include "ralrimivv.mm"
include "dfwe2.mm"
include "sylanbrc.mm"
include "fpwwe2cbv.mm"
include "simpr.mm"
include "fpwwe2lem3.mm"
include "anasss.mm"
include "cnvimass.mm"
include "ssexd.mm"
include "xpexg.mm"
include "dmexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "id.mm"
include "olc.mm"
include "syl6.mm"
include "imp.mm"
include "a1d.mm"
include "elequ1.mm"
include "biimprd.mm"
include "jaodan.mm"
include "impr.mm"
include "jctird.mm"
include "syl6ibr.mm"
include "ancld.mm"
include "brin.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "com24.mm"
include "sylan2.mm"
include "breq2.mm"
include "imbi12d.mm"
include "ceqsalv.mm"
include "impbid.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "sylan9eqr.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "wrel.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "anbi12d.mm"
include "orc.mm"
include "adantrl.mm"
include "sylan2b.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr3i.mm"
include "eqrelrdv.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "sbcied.mm"
include "ralrimiv.mm"
include "mpbir2and.mm"

theorem fpwwe2lem12
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cF: class F
  let cW: class W
  let cX: class X
  let vr: setvar r
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cR: class R
  let cY: class Y
  let cS: class S
  assume fpwwe2.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ]. ( u F ( r i^i ( u X. u ) ) ) = y ) ) }
  assume fpwwe2.2: |- ( ph -> A e. _V )
  assume fpwwe2.3: |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) -> ( x F r ) e. A )
  assume fpwwe2.4: |- X = U. dom W

  disjoint u y
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint u x
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X r
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint ph r
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint A r
  disjoint A x
  disjoint W r
  disjoint W u
  disjoint W x
  disjoint W y
  disjoint B u
  disjoint B y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint r s
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint a n
  disjoint X a
  disjoint b n
  disjoint X b
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint X n
  disjoint X s
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint M r
  disjoint M u
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint N r
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint a ph
  disjoint b ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint A a
  disjoint A s
  disjoint A t
  disjoint A w
  disjoint A z
  disjoint R r
  disjoint R u
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint Y r
  disjoint Y u
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint S r
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint W a
  disjoint W b
  disjoint W n
  disjoint W s
  disjoint W t
  disjoint W v
  disjoint W w
  disjoint W z
  assert |- ( ph -> X e. dom W )

  proof
    wph
    cX
    cW
    crn
    #
    cuni
    #
    cW
    wbr
    #
    cX
    cW
    cdm
    #
    wcel
    wph
    @2
    cX
    cA
    wss
    #
    @1
    cX
    cX
    cxp
    #
    wss
    #
    wa
    cX
    @1
    wwe
    #
    vu
    cv
    #
    @1
    @8
    @8
    cxp
    #
    cin
    #
    cF
    co
    #
    vy
    cv
    #
    wceq
    #
    vu
    @1
    ccnv
    @12
    csn
    #
    cima
    #
    wsbc
    #
    vy
    cX
    wral
    #
    wa
    wph
    @4
    @6
    wph
    cX
    @3
    cuni
    #
    cA
    fpwwe2.4
    wph
    @3
    cA
    cpw
    #
    wss
    @18
    cA
    wss
    wph
    va
    @3
    @19
    va
    cv
    #
    @3
    wcel
    #
    @20
    vs
    cv
    #
    cW
    wbr
    #
    vs
    wex
    #
    wph
    @20
    @19
    wcel
    #
    vs
    @20
    cW
    va
    vex
    #
    eldm
    #
    wph
    @23
    @25
    vs
    wph
    @23
    @25
    wph
    @23
    wa
    #
    @20
    cA
    wss
    #
    @25
    @28
    @29
    @22
    @20
    @20
    cxp
    #
    wss
    #
    wph
    @23
    @29
    @31
    wa
    #
    @20
    @22
    wwe
    #
    @8
    @22
    @9
    cin
    cF
    co
    @12
    wceq
    vu
    @22
    ccnv
    @14
    cima
    #
    wsbc
    vy
    @20
    wral
    #
    wa
    #
    wph
    vx
    vy
    vu
    cA
    @22
    cF
    cW
    @20
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    #
    simprbda
    #
    simpld
    va
    cA
    selpw
    sylibr
    ex
    exlimdv
    syl5bi
    ssrdv
    @3
    cA
    sspwuni
    sylib
    syl5eqss
    #
    wph
    @0
    @5
    cpw
    #
    wss
    @6
    wph
    vs
    @0
    @40
    @22
    @0
    wcel
    #
    @23
    va
    wex
    wph
    @22
    @40
    wcel
    #
    va
    @22
    cW
    vs
    vex
    elrn
    wph
    @23
    @42
    va
    wph
    @23
    @42
    @28
    @22
    @5
    wss
    @42
    @28
    @22
    @30
    @5
    @28
    @29
    @31
    @38
    simprd
    #
    @28
    @20
    cX
    wss
    #
    @44
    @30
    @5
    wss
    @28
    @20
    @18
    cX
    @28
    @21
    @20
    @18
    wss
    @23
    @21
    wph
    @20
    @22
    cW
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @45
    @45
    cxp
    wss
    #
    wa
    @45
    @47
    wwe
    #
    @8
    @47
    @9
    cin
    cF
    co
    @12
    wceq
    vu
    @47
    ccnv
    @14
    cima
    wsbc
    vy
    @45
    wral
    wa
    wa
    vx
    vr
    cW
    fpwwe2.1
    relopabi
    #
    releldmi
    adantl
    @20
    @3
    elssuni
    syl
    fpwwe2.4
    syl6sseqr
    #
    @51
    @20
    cX
    @20
    cX
    xpss12
    syl2anc
    sstrd
    vs
    @5
    selpw
    sylibr
    ex
    exlimdv
    syl5bi
    ssrdv
    @0
    @5
    sspwuni
    sylib
    #
    jca
    wph
    @7
    @17
    wph
    cX
    @1
    wfr
    #
    @12
    vw
    cv
    #
    @1
    wbr
    #
    vy
    vw
    weq
    #
    @54
    @12
    @1
    wbr
    #
    w3o
    #
    vw
    cX
    wral
    vy
    cX
    wral
    @7
    wph
    vn
    cv
    #
    cX
    wss
    #
    @59
    c0
    wne
    #
    wa
    @54
    vv
    cv
    #
    @1
    wbr
    #
    wn
    #
    vw
    @59
    wral
    #
    vv
    @59
    wrex
    #
    wi
    #
    vn
    wal
    @53
    wph
    @67
    vn
    wph
    @60
    @61
    @66
    @61
    vy
    vn
    wel
    #
    vy
    wex
    wph
    @60
    wa
    #
    @66
    vy
    @59
    n0
    @69
    @68
    @66
    vy
    wph
    @60
    @68
    @66
    wph
    @60
    @68
    wa
    #
    wa
    #
    vy
    va
    wel
    #
    va
    @3
    wrex
    #
    @66
    @71
    @12
    cX
    wcel
    #
    @73
    @70
    @74
    wph
    @59
    cX
    @12
    ssel2
    adantl
    @74
    @12
    @18
    wcel
    @73
    cX
    @18
    @12
    fpwwe2.4
    eleq2i
    va
    @12
    @3
    eluni2
    bitri
    #
    sylib
    @71
    @72
    @66
    va
    @3
    @21
    @24
    @71
    @72
    @66
    wi
    #
    @27
    @71
    @23
    @76
    vs
    @71
    @23
    @72
    @66
    @71
    @23
    @72
    wa
    #
    wa
    #
    vz
    cv
    #
    @62
    @22
    wbr
    #
    wn
    vz
    @59
    @20
    cin
    #
    wral
    #
    vv
    @81
    wrex
    #
    @66
    @78
    @81
    cvv
    wcel
    #
    @20
    @22
    wfr
    #
    @81
    @20
    wss
    #
    @81
    c0
    wne
    #
    @83
    @84
    @78
    @20
    @59
    @26
    inex2
    a1i
    @78
    @33
    @85
    wph
    @23
    @33
    @70
    @72
    @28
    @33
    @35
    wph
    @23
    @32
    @36
    @37
    simplbda
    simpld
    #
    ad2ant2r
    @20
    @22
    wefr
    syl
    @86
    @78
    @59
    @20
    inss2
    #
    a1i
    @78
    @68
    @72
    @87
    wph
    @60
    @68
    @77
    simplrr
    @71
    @23
    @72
    simprr
    @12
    @59
    @20
    inelcm
    syl2anc
    vv
    vz
    @20
    @81
    cvv
    @22
    fri
    syl22anc
    @78
    @82
    @65
    vv
    @81
    @59
    @78
    @62
    @81
    wcel
    #
    @82
    wa
    #
    vv
    vn
    wel
    #
    @65
    wa
    @78
    @91
    wa
    #
    @92
    @65
    @93
    @81
    @59
    @62
    @59
    @20
    inss1
    @78
    @90
    @82
    simprl
    #
    sseldi
    @93
    @64
    vw
    @59
    @93
    vw
    vn
    wel
    #
    wa
    #
    @63
    @80
    vz
    @81
    wrex
    #
    @96
    @82
    @97
    wn
    @78
    @90
    @82
    @95
    simplrr
    @80
    vz
    @81
    ralnex
    sylib
    @63
    @54
    @62
    cop
    #
    vt
    cv
    #
    wcel
    #
    vt
    @0
    wrex
    #
    @96
    @97
    @63
    @98
    @1
    wcel
    @101
    @54
    @62
    @1
    df-br
    vt
    @98
    @0
    eluni2
    bitri
    @96
    @100
    @97
    vt
    @0
    @99
    @0
    wcel
    #
    vb
    cv
    #
    @99
    cW
    wbr
    #
    vb
    wex
    #
    @96
    @100
    @97
    wi
    #
    vb
    @99
    cW
    vt
    vex
    elrn
    #
    @96
    @104
    @106
    vb
    @93
    @95
    @104
    @106
    @100
    @54
    @62
    @99
    wbr
    #
    @93
    @95
    @104
    wa
    #
    wa
    @97
    @54
    @62
    @99
    df-br
    @93
    @109
    @108
    @97
    @93
    @109
    @108
    wa
    #
    wa
    #
    @20
    @103
    wss
    #
    @22
    @99
    @103
    @20
    cxp
    #
    cin
    #
    wceq
    #
    wa
    #
    @97
    @103
    @20
    wss
    #
    @99
    @22
    @20
    @103
    cxp
    #
    cin
    #
    wceq
    #
    wa
    #
    @111
    @116
    wa
    #
    @54
    @81
    wcel
    #
    @54
    @62
    @22
    wbr
    #
    @97
    @122
    @59
    @20
    @54
    @111
    @95
    @116
    @93
    @95
    @104
    @108
    simprll
    #
    adantr
    @122
    @54
    @62
    @30
    wbr
    #
    vw
    va
    wel
    #
    @122
    @124
    @126
    @122
    @124
    @54
    @62
    @114
    wbr
    #
    @122
    vw
    vb
    wel
    #
    vv
    va
    wel
    #
    @108
    @128
    @111
    @129
    @116
    @111
    @54
    @62
    @103
    @103
    cxp
    #
    wbr
    #
    @129
    @111
    @108
    @132
    @93
    @109
    @108
    simprr
    @111
    @99
    @131
    @54
    @62
    @111
    wph
    @23
    @104
    @99
    @131
    wss
    #
    wph
    @70
    @77
    @91
    @110
    simp-4l
    #
    @78
    @23
    @91
    @110
    @71
    @23
    @72
    simprl
    ad2antrr
    #
    @93
    @95
    @104
    @108
    simprlr
    #
    wph
    @23
    @104
    wa
    #
    wa
    #
    @103
    cA
    wss
    #
    @133
    @138
    @139
    @133
    wa
    #
    @103
    @99
    wwe
    #
    @8
    @99
    @9
    cin
    cF
    co
    @12
    wceq
    vu
    @99
    ccnv
    @14
    cima
    wsbc
    vy
    @103
    wral
    #
    wa
    #
    @138
    @104
    @140
    @143
    wa
    #
    wph
    @23
    @104
    simprr
    #
    wph
    @104
    @144
    wb
    @137
    wph
    vx
    vy
    vu
    cA
    @99
    cF
    cW
    @103
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    adantr
    mpbid
    #
    simpld
    simprd
    #
    syl12anc
    ssbrd
    mpd
    @132
    @129
    vv
    vb
    wel
    @54
    @62
    @103
    @103
    brxp
    simplbi
    syl
    #
    adantr
    @93
    @130
    @110
    @116
    @93
    @81
    @20
    @62
    @89
    @94
    sseldi
    ad2antrr
    @93
    @109
    @108
    @116
    simplrr
    @54
    @62
    @103
    @20
    @99
    brinxp2
    syl3anbrc
    @122
    @22
    @114
    @54
    @62
    @111
    @112
    @115
    simprr
    breqd
    mpbird
    #
    @122
    @22
    @30
    @54
    @62
    @111
    @31
    @116
    @111
    wph
    @23
    @31
    @134
    @135
    @43
    syl2anc
    adantr
    ssbrd
    mpd
    @126
    @127
    @130
    @54
    @62
    @20
    @20
    brxp
    simplbi
    syl
    elind
    @149
    @80
    @124
    vz
    @54
    @81
    @79
    @54
    @62
    @22
    breq1
    rspcev
    #
    syl2anc
    @111
    @121
    wa
    #
    @123
    @124
    @97
    @151
    @59
    @20
    @54
    @111
    @95
    @121
    @125
    adantr
    @151
    @103
    @20
    @54
    @111
    @117
    @120
    simprl
    @111
    @129
    @121
    @148
    adantr
    sseldd
    elind
    @151
    @108
    @124
    @93
    @109
    @108
    @121
    simplrr
    @151
    @99
    @22
    @54
    @62
    @151
    @99
    @119
    @22
    @111
    @117
    @120
    simprr
    @22
    @118
    inss1
    #
    syl6eqss
    ssbrd
    mpd
    @150
    syl2anc
    @111
    wph
    @23
    @104
    @116
    @121
    wo
    #
    @134
    @135
    @136
    @138
    vx
    vy
    vu
    cA
    @22
    @99
    cF
    cW
    @20
    @103
    vr
    fpwwe2.1
    wph
    cA
    cvv
    wcel
    #
    @137
    fpwwe2.2
    adantr
    wph
    @46
    @48
    @49
    w3a
    @45
    @47
    cF
    co
    cA
    wcel
    @137
    fpwwe2.3
    adantlr
    wph
    @23
    @104
    simprl
    @145
    fpwwe2lem10
    #
    syl12anc
    mpjaodan
    expr
    syl5bir
    expr
    exlimdv
    syl5bi
    rexlimdv
    syl5bi
    mtod
    ralrimiva
    jca
    ex
    reximdv2
    mpd
    exp32
    exlimdv
    syl5bi
    rexlimdv
    mpd
    expr
    exlimdv
    syl5bi
    expimpd
    alrimiv
    vn
    vv
    vw
    cX
    @1
    df-fr
    sylibr
    wph
    @58
    vy
    vw
    cX
    cX
    @74
    @54
    cX
    wcel
    #
    wa
    #
    @72
    @129
    wa
    #
    vb
    @3
    wrex
    va
    @3
    wrex
    #
    wph
    @58
    @157
    @73
    @129
    vb
    @3
    wrex
    #
    wa
    @159
    @74
    @73
    @156
    @160
    @75
    @156
    @54
    @18
    wcel
    @160
    cX
    @18
    @54
    fpwwe2.4
    eleq2i
    vb
    @54
    @3
    eluni2
    bitri
    anbi12i
    @72
    @129
    va
    vb
    @3
    @3
    reeanv
    bitr4i
    wph
    @158
    @58
    va
    vb
    @3
    @3
    @21
    @103
    @3
    wcel
    #
    wa
    #
    @137
    vt
    wex
    vs
    wex
    #
    wph
    @158
    @58
    wi
    #
    @162
    @24
    @104
    vt
    wex
    #
    wa
    @163
    @21
    @24
    @161
    @165
    @27
    vt
    @103
    cW
    vb
    vex
    eldm
    anbi12i
    @23
    @104
    vs
    vt
    eeanv
    bitr4i
    wph
    @137
    @164
    vs
    vt
    wph
    @137
    @158
    @58
    @138
    @158
    wa
    #
    @116
    @58
    @121
    @166
    @116
    wa
    #
    @12
    @54
    @99
    wbr
    #
    @56
    @54
    @12
    @99
    wbr
    #
    w3o
    #
    @58
    @167
    @103
    @99
    wor
    #
    vy
    vb
    wel
    @129
    @170
    @167
    @141
    @171
    @138
    @141
    @158
    @116
    @138
    @141
    @142
    @138
    @140
    @143
    @146
    simprd
    simpld
    ad2antrr
    @103
    @99
    weso
    syl
    @167
    @20
    @103
    @12
    @166
    @112
    @115
    simprl
    @138
    @72
    @129
    @116
    simplrl
    sseldd
    @138
    @72
    @129
    @116
    simplrr
    @103
    @12
    @54
    @99
    solin
    syl12anc
    @167
    @168
    @55
    @56
    @56
    @169
    @57
    @167
    @99
    @1
    @12
    @54
    @167
    @102
    @99
    @1
    wss
    @138
    @102
    @158
    @116
    @104
    @102
    wph
    @23
    @103
    @99
    cW
    @50
    relelrni
    ad2antll
    ad2antrr
    @99
    @0
    elssuni
    syl
    #
    ssbrd
    @167
    @56
    idd
    @167
    @99
    @1
    @54
    @12
    @172
    ssbrd
    3orim123d
    mpd
    @166
    @121
    wa
    #
    @12
    @54
    @22
    wbr
    #
    @56
    @54
    @12
    @22
    wbr
    #
    w3o
    #
    @58
    @173
    @20
    @22
    wor
    #
    @72
    @127
    @176
    @173
    @33
    @177
    @138
    @33
    @158
    @121
    wph
    @23
    @33
    @104
    @88
    adantrr
    ad2antrr
    @20
    @22
    weso
    syl
    @138
    @72
    @129
    @121
    simplrl
    @173
    @103
    @20
    @54
    @166
    @117
    @120
    simprl
    @138
    @72
    @129
    @121
    simplrr
    sseldd
    @20
    @12
    @54
    @22
    solin
    syl12anc
    @173
    @174
    @55
    @56
    @56
    @175
    @57
    @173
    @22
    @1
    @12
    @54
    @173
    @41
    @22
    @1
    wss
    #
    @138
    @41
    @158
    @121
    @23
    @41
    wph
    @104
    @20
    @22
    cW
    @50
    relelrni
    #
    ad2antrl
    ad2antrr
    @22
    @0
    elssuni
    #
    syl
    #
    ssbrd
    @173
    @56
    idd
    @173
    @22
    @1
    @54
    @12
    @181
    ssbrd
    3orim123d
    mpd
    @138
    @153
    @158
    @155
    adantr
    mpjaodan
    exp31
    exlimdvv
    syl5bi
    rexlimdvv
    syl5bi
    ralrimivv
    vy
    vw
    cX
    @1
    dfwe2
    sylanbrc
    wph
    @16
    vy
    cX
    @74
    @73
    wph
    @16
    @75
    wph
    @72
    @16
    va
    @3
    @21
    @24
    wph
    @72
    @16
    wi
    #
    @27
    wph
    @23
    @182
    vs
    wph
    @23
    @72
    @16
    wph
    @77
    wa
    #
    @16
    @34
    @22
    @34
    @34
    cxp
    #
    cin
    #
    cF
    co
    #
    @12
    wceq
    #
    wph
    @23
    @72
    @187
    @28
    vz
    vw
    vb
    cA
    @12
    @22
    cF
    cW
    @20
    vt
    vx
    vy
    vw
    vb
    vu
    cA
    cF
    cW
    vt
    vr
    vz
    fpwwe2.1
    fpwwe2cbv
    wph
    @154
    @23
    fpwwe2.2
    adantr
    wph
    @23
    simpr
    fpwwe2lem3
    anasss
    @183
    @13
    @187
    vu
    @15
    cvv
    @183
    @15
    @1
    cdm
    #
    wss
    @188
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @1
    @14
    cnvimass
    @183
    @1
    cvv
    wcel
    #
    @189
    wph
    @190
    @77
    wph
    @1
    @5
    cvv
    wph
    cX
    cvv
    wcel
    #
    @191
    @5
    cvv
    wcel
    wph
    cX
    cA
    cvv
    fpwwe2.2
    @39
    ssexd
    #
    @192
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    @52
    ssexd
    adantr
    @1
    cvv
    dmexg
    syl
    @15
    @188
    cvv
    ssexg
    sylancr
    @183
    @8
    @15
    wceq
    #
    wa
    #
    @11
    @186
    @12
    @194
    @8
    @34
    @10
    @185
    cF
    @193
    @183
    @8
    @15
    @34
    @193
    id
    @183
    vz
    @15
    @34
    @183
    @79
    @12
    @1
    wbr
    #
    @79
    @12
    @22
    wbr
    #
    @79
    @15
    wcel
    #
    @79
    @34
    wcel
    #
    @183
    @195
    @196
    @183
    vw
    vy
    weq
    #
    @79
    @54
    @1
    wbr
    #
    @79
    @54
    @22
    wbr
    #
    wi
    #
    wi
    #
    vw
    wal
    @195
    @196
    wi
    #
    @183
    @203
    vw
    @183
    @199
    @202
    @199
    @183
    @175
    @199
    wo
    #
    @202
    @199
    @175
    olc
    @200
    @79
    @54
    cop
    #
    @99
    wcel
    #
    vt
    @0
    wrex
    #
    @183
    @205
    wa
    #
    @201
    @200
    @206
    @1
    wcel
    @208
    @79
    @54
    @1
    df-br
    vt
    @206
    @0
    eluni2
    bitri
    @209
    @207
    @201
    vt
    @0
    @102
    @105
    @209
    @207
    @201
    wi
    #
    @107
    @209
    @104
    @210
    vb
    @183
    @205
    @104
    @210
    wi
    #
    wph
    @23
    @72
    @205
    @211
    wi
    @28
    @104
    @205
    @72
    @210
    wph
    @23
    @104
    @205
    @72
    @210
    wi
    wi
    @138
    @205
    @72
    @210
    @207
    @79
    @54
    @99
    wbr
    #
    @138
    @205
    @72
    wa
    #
    wa
    #
    @201
    @79
    @54
    @99
    df-br
    @214
    @116
    @212
    @201
    wi
    @121
    @214
    @116
    wa
    #
    @212
    @212
    @79
    @54
    @113
    wbr
    #
    wa
    #
    @201
    @215
    @212
    @216
    @215
    @212
    vz
    vb
    wel
    #
    @127
    wa
    @216
    @215
    @212
    @218
    @127
    @215
    @212
    @79
    @54
    @131
    wbr
    #
    @218
    @215
    @99
    @131
    @79
    @54
    @138
    @133
    @213
    @116
    @147
    ad2antrr
    ssbrd
    @219
    @218
    @129
    @79
    @54
    @103
    @103
    brxp
    simplbi
    syl6
    @214
    @127
    @116
    @138
    @205
    @72
    @127
    @138
    @175
    @72
    @127
    wi
    #
    @199
    @138
    @175
    wa
    #
    @127
    @72
    @221
    @54
    @12
    @30
    wbr
    #
    @127
    @138
    @175
    @222
    @138
    @22
    @30
    @54
    @12
    wph
    @23
    @31
    @104
    @43
    adantrr
    ssbrd
    imp
    @222
    @127
    @72
    @54
    @12
    @20
    @20
    brxp
    simplbi
    syl
    a1d
    @199
    @220
    @138
    @199
    @127
    @72
    vw
    vy
    va
    elequ1
    biimprd
    adantl
    jaodan
    impr
    adantr
    jctird
    @79
    @54
    @103
    @20
    brxp
    syl6ibr
    ancld
    @215
    @201
    @79
    @54
    @114
    wbr
    @217
    @215
    @22
    @114
    @79
    @54
    @214
    @112
    @115
    simprr
    breqd
    @79
    @54
    @99
    @113
    brin
    syl6bb
    sylibrd
    @214
    @121
    wa
    #
    @99
    @22
    @79
    @54
    @223
    @99
    @119
    @22
    @214
    @117
    @120
    simprr
    @152
    syl6eqss
    ssbrd
    @138
    @153
    @213
    @155
    adantr
    mpjaodan
    syl5bir
    exp32
    expr
    com24
    impr
    imp
    exlimdv
    syl5bi
    rexlimdv
    syl5bi
    #
    sylan2
    ex
    alrimiv
    @202
    @204
    vw
    @12
    vy
    vex
    #
    @199
    @200
    @195
    @201
    @196
    @54
    @12
    @79
    @1
    breq2
    @54
    @12
    @79
    @22
    breq2
    imbi12d
    ceqsalv
    sylib
    @183
    @22
    @1
    @79
    @12
    @183
    @41
    @178
    @23
    @41
    wph
    @72
    @179
    ad2antrl
    @180
    syl
    #
    ssbrd
    impbid
    @12
    cvv
    wcel
    #
    @197
    @195
    wb
    @225
    @1
    @12
    @79
    cvv
    vz
    vex
    #
    eliniseg
    ax-mp
    @227
    @198
    @196
    wb
    @225
    @22
    @12
    @79
    cvv
    @228
    eliniseg
    #
    ax-mp
    3bitr4g
    eqrdv
    sylan9eqr
    #
    @194
    @10
    @1
    @184
    cin
    #
    @185
    @194
    @9
    @184
    @1
    @194
    @8
    @34
    @230
    sqxpeqd
    ineq2d
    @183
    @231
    @185
    wceq
    @193
    @183
    vz
    vw
    @231
    @185
    @231
    @184
    wss
    @184
    wrel
    #
    @231
    wrel
    @1
    @184
    inss2
    @34
    @34
    relxp
    #
    @231
    @184
    relss
    mp2
    @185
    @184
    wss
    @232
    @185
    wrel
    @22
    @184
    inss2
    @233
    @185
    @184
    relss
    mp2
    @183
    @198
    @54
    @34
    wcel
    #
    wa
    #
    @200
    wa
    #
    @235
    @201
    wa
    #
    @206
    @231
    wcel
    #
    @206
    @185
    wcel
    #
    @183
    @235
    @200
    @201
    @235
    @183
    @196
    @175
    wa
    #
    @200
    @201
    wb
    @227
    @235
    @240
    wb
    @225
    @227
    @198
    @196
    @234
    @175
    @229
    @22
    @12
    @54
    cvv
    vw
    vex
    eliniseg
    anbi12d
    ax-mp
    @183
    @240
    wa
    #
    @200
    @201
    @183
    @175
    @202
    @196
    @175
    @183
    @205
    @202
    @175
    @199
    orc
    @224
    sylan2
    adantrl
    @241
    @22
    @1
    @79
    @54
    @183
    @178
    @240
    @226
    adantr
    ssbrd
    impbid
    sylan2b
    pm5.32da
    @79
    @54
    @231
    wbr
    @198
    @234
    @200
    w3a
    @238
    @236
    @79
    @54
    @34
    @34
    @1
    brinxp2
    @79
    @54
    @231
    df-br
    @198
    @234
    @200
    df-3an
    3bitr3i
    @79
    @54
    @185
    wbr
    @198
    @234
    @201
    w3a
    @239
    @237
    @79
    @54
    @34
    @34
    @22
    brinxp2
    @79
    @54
    @185
    df-br
    @198
    @234
    @201
    df-3an
    3bitr3i
    3bitr4g
    eqrelrdv
    adantr
    eqtrd
    oveq12d
    eqeq1d
    sbcied
    mpbird
    exp32
    exlimdv
    syl5bi
    rexlimdv
    syl5bi
    ralrimiv
    jca
    wph
    vx
    vy
    vu
    cA
    @1
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    mpbir2and
    cX
    @1
    cW
    @50
    releldmi
    syl
end
