include "wbr.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cfv.mm"
include "cdm.mm"
include "wss.mm"
include "wfun.mm"
include "wb.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "fpwwe2lem11.mm"
include "ffun.mm"
include "syl.mm"
include "funbrfv2b.mm"
include "simprbda.mm"
include "adantrr.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "cin.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "cdif.mm"
include "c0.mm"
include "simplrr.mm"
include "wne.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wfr.mm"
include "adantr.mm"
include "wwe.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wsbc.mm"
include "fpwwe2lem12.mm"
include "funfvbrb.mm"
include "mpbid.mm"
include "fpwwe2lem2.mm"
include "ad2antrr.mm"
include "simpld.mm"
include "ssexd.mm"
include "difexg.mm"
include "simprd.mm"
include "wefr.mm"
include "difssd.mm"
include "fri.mm"
include "expr.mm"
include "syl21anc.mm"
include "ssdif0.mm"
include "indif1.mm"
include "eqeq1i.mm"
include "disj.mm"
include "vex.mm"
include "eliniseg.mm"
include "ax-mp.mm"
include "notbii.mm"
include "ralbii.mm"
include "bitri.mm"
include "3bitr2i.mm"
include "cnvimass.mm"
include "dmss.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "syl5ss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "sseq1d.mm"
include "syl5bbr.mm"
include "rexbidv.mm"
include "eldifn.mm"
include "ad2antrl.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "imp.mm"
include "simprr.mm"
include "breqd.mm"
include "eldifi.mm"
include "simpr.mm"
include "brxp.mm"
include "sylanbrc.mm"
include "brin.mm"
include "rbaib.mm"
include "bitrd.mm"
include "biimpa.mm"
include "ad3antrrr.mm"
include "ssbrd.mm"
include "simplbi.mm"
include "syl6.mm"
include "sylbird.mm"
include "mtod.mm"
include "wor.mm"
include "weso.mm"
include "sselda.mm"
include "wo.mm"
include "sotric.mm"
include "ioran.mm"
include "syl6bb.mm"
include "syl12anc.mm"
include "mpbir2and.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "in32.mm"
include "ineq1d.mm"
include "df-ss.mm"
include "eqtr3d.mm"
include "inss2.mm"
include "xpss1.mm"
include "3eqtr3a.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "fpwwe2lem3.mm"
include "mpdan.mm"
include "eqneltrd.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "syld.mm"
include "necon4ad.mm"
include "mpd.mm"
include "w3a.mm"
include "adantlr.mm"
include "simprl.mm"
include "fpwwe2lem10.mm"
include "mpjaod.mm"
include "eqbrtrrd.mm"
include "funbrfv.mm"
include "sylc.mm"
include "eqcomd.mm"
include "jca.mm"
include "fpwwe2lem13.mm"
include "breq12.mm"
include "oveq12.mm"
include "eleq12d.mm"
include "anbi12d.mm"
include "impbid.mm"

theorem fpwwe2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
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
  disjoint R r
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint Y r
  disjoint Y u
  disjoint Y x
  disjoint Y y
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
  disjoint R w
  disjoint R z
  disjoint Y w
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
  assert |- ( ph -> ( ( Y W R /\ ( Y F R ) e. Y ) <-> ( Y = X /\ R = ( W ` X ) ) ) )

  proof
    wph
    cY
    cR
    cW
    wbr
    #
    cY
    cR
    cF
    co
    #
    cY
    wcel
    #
    wa
    #
    cY
    cX
    wceq
    #
    cR
    cX
    cW
    cfv
    #
    wceq
    #
    wa
    #
    wph
    @3
    @7
    wph
    @3
    wa
    #
    @4
    @6
    @8
    cY
    cX
    @8
    cY
    cW
    cdm
    #
    wcel
    #
    cY
    cX
    wss
    #
    wph
    @0
    @10
    @2
    wph
    @0
    @10
    cY
    cW
    cfv
    cR
    wceq
    #
    wph
    cW
    wfun
    #
    @0
    @10
    @12
    wa
    wb
    wph
    @9
    cX
    cX
    cxp
    #
    cpw
    #
    cW
    wf
    @13
    wph
    vx
    vy
    vu
    cA
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2.3
    fpwwe2.4
    fpwwe2lem11
    @9
    @15
    cW
    ffun
    syl
    #
    cY
    cR
    cW
    funbrfv2b
    syl
    simprbda
    adantrr
    @10
    cY
    @9
    cuni
    cX
    cY
    @9
    elssuni
    fpwwe2.4
    syl6sseqr
    syl
    #
    @8
    cX
    cY
    wss
    #
    @5
    cR
    cY
    cX
    cxp
    cin
    wceq
    #
    wa
    #
    @18
    @11
    cR
    @5
    cX
    cY
    cxp
    #
    cin
    #
    wceq
    #
    wa
    #
    @20
    @18
    wi
    @8
    @18
    @19
    simpl
    a1i
    @8
    @24
    @18
    @8
    @24
    wa
    #
    cX
    cY
    cdif
    #
    c0
    wceq
    #
    @18
    @25
    @2
    @27
    wph
    @0
    @2
    @24
    simplrr
    @25
    @2
    @26
    c0
    @25
    @26
    c0
    wne
    #
    vw
    cv
    #
    vz
    cv
    #
    @5
    wbr
    #
    wn
    #
    vw
    @26
    wral
    #
    vz
    @26
    wrex
    #
    @2
    wn
    #
    @25
    @26
    cvv
    wcel
    #
    cX
    @5
    wfr
    #
    @26
    cX
    wss
    #
    @28
    @34
    wi
    @25
    cX
    cvv
    wcel
    @36
    @25
    cX
    cA
    cvv
    @8
    cA
    cvv
    wcel
    #
    @24
    wph
    @39
    @3
    fpwwe2.2
    adantr
    #
    adantr
    #
    @25
    cX
    cA
    wss
    #
    @5
    @14
    wss
    #
    @25
    @42
    @43
    wa
    #
    cX
    @5
    wwe
    #
    vu
    cv
    #
    @5
    @46
    @46
    cxp
    #
    cin
    cF
    co
    vy
    cv
    #
    wceq
    vu
    @5
    ccnv
    #
    @48
    csn
    #
    cima
    wsbc
    vy
    cX
    wral
    #
    wa
    #
    wph
    @44
    @52
    wa
    #
    @3
    @24
    wph
    cX
    @5
    cW
    wbr
    #
    @53
    wph
    cX
    @9
    wcel
    #
    @54
    wph
    vx
    vy
    vu
    cA
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2.3
    fpwwe2.4
    fpwwe2lem12
    wph
    @13
    @55
    @54
    wb
    @16
    cX
    cW
    funfvbrb
    syl
    mpbid
    #
    wph
    vx
    vy
    vu
    cA
    @5
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    mpbid
    ad2antrr
    #
    simpld
    #
    simpld
    ssexd
    cX
    cY
    cvv
    difexg
    syl
    @25
    @45
    @37
    @25
    @45
    @51
    @25
    @44
    @52
    @57
    simprd
    simpld
    #
    cX
    @5
    wefr
    syl
    @25
    cX
    cY
    difssd
    @36
    @37
    wa
    @38
    @28
    @34
    vz
    vw
    cX
    @26
    cvv
    @5
    fri
    expr
    syl21anc
    @25
    @34
    @49
    @30
    csn
    #
    cima
    #
    cY
    wss
    #
    vz
    @26
    wrex
    @35
    @25
    @33
    @62
    vz
    @26
    @33
    cX
    @61
    cin
    #
    cY
    wss
    #
    @25
    @62
    @64
    @63
    cY
    cdif
    #
    c0
    wceq
    @26
    @61
    cin
    #
    c0
    wceq
    #
    @33
    @63
    cY
    ssdif0
    @66
    @65
    c0
    cX
    @61
    cY
    indif1
    eqeq1i
    @67
    @29
    @61
    wcel
    #
    wn
    #
    vw
    @26
    wral
    @33
    vw
    @26
    @61
    disj
    @69
    @32
    vw
    @26
    @68
    @31
    @30
    cvv
    wcel
    @68
    @31
    wb
    vz
    vex
    @5
    @30
    @29
    cvv
    vw
    vex
    eliniseg
    ax-mp
    #
    notbii
    ralbii
    bitri
    3bitr2i
    @25
    @63
    @61
    cY
    @25
    @61
    cX
    wss
    @63
    @61
    wceq
    @25
    @61
    @5
    cdm
    #
    cX
    @5
    @60
    cnvimass
    @25
    @71
    @14
    cdm
    #
    cX
    @25
    @43
    @71
    @72
    wss
    @25
    @42
    @43
    @58
    simprd
    @5
    @14
    dmss
    syl
    cX
    dmxpid
    syl6sseq
    syl5ss
    @61
    cX
    sseqin2
    sylib
    sseq1d
    syl5bbr
    rexbidv
    @25
    @62
    @35
    vz
    @26
    @25
    @30
    @26
    wcel
    #
    @62
    wa
    #
    wa
    #
    @1
    @30
    cY
    @75
    @1
    @61
    @5
    @61
    @61
    cxp
    #
    cin
    #
    cF
    co
    #
    @30
    @75
    cY
    @61
    cR
    @77
    cF
    @75
    cY
    @61
    @75
    vw
    cY
    @61
    @75
    @29
    cY
    wcel
    #
    @68
    @75
    @79
    wa
    #
    @31
    @68
    @80
    @31
    @29
    @30
    wceq
    #
    wn
    #
    @30
    @29
    @5
    wbr
    #
    wn
    #
    @75
    @79
    @82
    @75
    @81
    @79
    @75
    @79
    wn
    @81
    @30
    cY
    wcel
    #
    wn
    #
    @73
    @86
    @25
    @62
    @30
    cX
    cY
    eldifn
    ad2antrl
    #
    @81
    @79
    @85
    @29
    @30
    cY
    eleq1
    notbid
    syl5ibrcom
    con2d
    imp
    @80
    @83
    @85
    @75
    @86
    @79
    @87
    adantr
    @80
    @83
    @30
    @29
    cR
    wbr
    #
    @85
    @80
    @88
    @30
    @29
    @22
    wbr
    #
    @83
    @80
    cR
    @22
    @30
    @29
    @25
    @23
    @74
    @79
    @8
    @11
    @23
    simprr
    ad2antrr
    breqd
    @80
    @30
    @29
    @21
    wbr
    #
    @89
    @83
    wb
    @80
    @30
    cX
    wcel
    #
    @79
    @90
    @75
    @91
    @79
    @73
    @91
    @25
    @62
    @30
    cX
    cY
    eldifi
    ad2antrl
    #
    adantr
    #
    @75
    @79
    simpr
    @30
    @29
    cX
    cY
    brxp
    sylanbrc
    @89
    @83
    @90
    @30
    @29
    @5
    @21
    brin
    rbaib
    syl
    bitrd
    @80
    @88
    @30
    @29
    cY
    cY
    cxp
    #
    wbr
    #
    @85
    @80
    cR
    @94
    @30
    @29
    @8
    cR
    @94
    wss
    #
    @24
    @74
    @79
    @8
    cY
    cA
    wss
    #
    @96
    @8
    @97
    @96
    wa
    #
    cY
    cR
    wwe
    @46
    cR
    @47
    cin
    cF
    co
    @48
    wceq
    vu
    cR
    ccnv
    @50
    cima
    wsbc
    vy
    cY
    wral
    wa
    #
    wph
    @0
    @98
    @99
    wa
    #
    @2
    wph
    @0
    @100
    wph
    vx
    vy
    vu
    cA
    cR
    cF
    cW
    cY
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2lem2
    biimpa
    adantrr
    simpld
    simprd
    #
    ad3antrrr
    ssbrd
    @95
    @85
    @79
    @30
    @29
    cY
    cY
    brxp
    simplbi
    syl6
    sylbird
    mtod
    @80
    cX
    @5
    wor
    #
    @29
    cX
    wcel
    #
    @91
    @31
    @82
    @84
    wa
    #
    wb
    @80
    @45
    @102
    @25
    @45
    @74
    @79
    @59
    ad2antrr
    cX
    @5
    weso
    syl
    @75
    cY
    cX
    @29
    @8
    @11
    @24
    @74
    @17
    ad2antrr
    #
    sselda
    @93
    @102
    @103
    @91
    wa
    wa
    @31
    @81
    @83
    wo
    wn
    @104
    cX
    @29
    @30
    @5
    sotric
    @81
    @83
    ioran
    syl6bb
    syl12anc
    mpbir2and
    @70
    sylibr
    ex
    ssrdv
    @25
    @73
    @62
    simprr
    eqssd
    #
    @75
    cR
    @5
    @94
    cin
    #
    @77
    @75
    @22
    @94
    cin
    #
    @107
    @21
    cin
    #
    cR
    @107
    @5
    @21
    @94
    in32
    @75
    cR
    @94
    cin
    #
    @108
    cR
    @75
    cR
    @22
    @94
    @8
    @11
    @23
    @74
    simplrr
    ineq1d
    @75
    @96
    @110
    cR
    wceq
    @8
    @96
    @24
    @74
    @101
    ad2antrr
    cR
    @94
    df-ss
    sylib
    eqtr3d
    @75
    @107
    @21
    wss
    @109
    @107
    wceq
    @75
    @107
    @94
    @21
    @5
    @94
    inss2
    @75
    @11
    @94
    @21
    wss
    @105
    cY
    cX
    cY
    xpss1
    syl
    syl5ss
    @107
    @21
    df-ss
    sylib
    3eqtr3a
    @75
    @94
    @76
    @5
    @75
    cY
    @61
    @106
    sqxpeqd
    ineq2d
    eqtrd
    oveq12d
    @75
    @91
    @78
    @30
    wceq
    @92
    @75
    vx
    vy
    vu
    cA
    @30
    @5
    cF
    cW
    cX
    vr
    fpwwe2.1
    @25
    @39
    @74
    @41
    adantr
    @8
    @54
    @24
    @74
    wph
    @54
    @3
    @56
    adantr
    #
    ad2antrr
    fpwwe2lem3
    mpdan
    eqtrd
    @87
    eqneltrd
    rexlimdvaa
    sylbid
    syld
    necon4ad
    mpd
    cX
    cY
    ssdif0
    sylibr
    ex
    @8
    vx
    vy
    vu
    cA
    @5
    cR
    cF
    cW
    cX
    cY
    vr
    fpwwe2.1
    @40
    wph
    vx
    cv
    #
    cA
    wss
    vr
    cv
    #
    @112
    @112
    cxp
    wss
    @112
    @113
    wwe
    w3a
    @112
    @113
    cF
    co
    cA
    wcel
    @3
    fpwwe2.3
    adantlr
    @111
    wph
    @0
    @2
    simprl
    #
    fpwwe2lem10
    mpjaod
    eqssd
    #
    @8
    @5
    cR
    @8
    @13
    cX
    cR
    cW
    wbr
    @5
    cR
    wceq
    wph
    @13
    @3
    @16
    adantr
    @8
    cY
    cX
    cR
    cW
    @115
    @114
    eqbrtrrd
    cX
    cR
    cW
    funbrfv
    sylc
    eqcomd
    jca
    ex
    wph
    @3
    @7
    @54
    cX
    @5
    cF
    co
    #
    cX
    wcel
    #
    wa
    wph
    @54
    @117
    @56
    wph
    vx
    vy
    vu
    cA
    cF
    cW
    cX
    vr
    fpwwe2.1
    fpwwe2.2
    fpwwe2.3
    fpwwe2.4
    fpwwe2lem13
    jca
    @7
    @0
    @54
    @2
    @117
    cY
    cX
    cR
    @5
    cW
    breq12
    @7
    @1
    @116
    cY
    cX
    cY
    cX
    cR
    @5
    cF
    oveq12
    @4
    @6
    simpl
    eleq12d
    anbi12d
    syl5ibrcom
    impbid
end
