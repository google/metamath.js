include "cv.mm"
include "cin.mm"
include "cxp.mm"
include "cordt.mm"
include "cfv.mm"
include "wcel.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "wa.mm"
include "inrab2.mm"
include "wceq.mm"
include "wss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "adantr.mm"
include "rabeq.mm"
include "syl.mm"
include "syl5eq.mm"
include "ctopon.mm"
include "cdm.mm"
include "cvv.mm"
include "ctsr.mm"
include "inex1g.mm"
include "eqid.mm"
include "ordttopon.mm"
include "cps.mm"
include "tsrps.mm"
include "psssdm.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "toponmax.mm"
include "wb.mm"
include "rabid2.mm"
include "eleq1.mm"
include "sylbir.mm"
include "syl5ibcom.mm"
include "wrex.mm"
include "dfrex2.mm"
include "breq1.mm"
include "cbvrexv.mm"
include "bitr3i.mm"
include "c0.mm"
include "ctop.mm"
include "ordttop.mm"
include "0opn.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "rabn0.mm"
include "notbid.mm"
include "bitri.mm"
include "wo.mm"
include "ad3antrrr.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "simpllr.mm"
include "tsrlin.mm"
include "syl3anc.mm"
include "ord.mm"
include "an4.mm"
include "wi.mm"
include "rabss.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "impr.mm"
include "sylan2b.mm"
include "brinxp.mm"
include "ancoms.mm"
include "rabbidva.mm"
include "eqtr4d.mm"
include "eleqtrrd.mm"
include "ordtopn1.mm"
include "eqeltrd.mm"
include "anassrs.mm"
include "expr.mm"
include "syld.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "rexlimdvaa.mm"
include "pm2.61d.mm"
include "ralrimiva.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "rabexg.mm"
include "ralrimivw.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ralrnmpt.mm"
include "mpbird.mm"

theorem ordtrest2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cR: class R
  let cX: class X
  let cV: class V
  assume ordtrest2.1: |- X = dom R
  assume ordtrest2.2: |- ( ph -> R e. TosetRel )
  assume ordtrest2.3: |- ( ph -> A C_ X )
  assume ordtrest2.4: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> { z e. X | ( x R z /\ z R y ) } C_ A )

  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
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
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint V x
  disjoint V y
  assert |- ( ph -> A. v e. ran ( z e. X |-> { w e. X | -. w R z } ) ( v i^i A ) e. ( ordTop ` ( R i^i ( A X. A ) ) ) )

  proof
    wph
    vv
    cv
    #
    cA
    cin
    #
    cR
    cA
    cA
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    wcel
    #
    vv
    vz
    cX
    vw
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    wn
    #
    vw
    cX
    crab
    #
    cmpt
    #
    crn
    wral
    #
    @10
    cA
    cin
    #
    @4
    wcel
    #
    vz
    cX
    wral
    #
    wph
    @14
    vz
    cX
    wph
    @7
    cX
    wcel
    #
    wa
    #
    @13
    @9
    vw
    cA
    crab
    #
    @4
    @17
    @13
    @9
    vw
    cX
    cA
    cin
    #
    crab
    #
    @18
    @9
    vw
    cX
    cA
    inrab2
    @17
    @19
    cA
    wceq
    #
    @20
    @18
    wceq
    wph
    @21
    @16
    wph
    cA
    cX
    wss
    #
    @21
    ordtrest2.3
    cA
    cX
    sseqin2
    sylib
    adantr
    @9
    vw
    @19
    cA
    rabeq
    syl
    syl5eq
    @17
    @9
    vw
    cA
    wral
    #
    @18
    @4
    wcel
    #
    @17
    cA
    @4
    wcel
    #
    @23
    @24
    wph
    @25
    @16
    wph
    @4
    cA
    ctopon
    cfv
    #
    wcel
    @25
    wph
    @4
    @3
    cdm
    #
    ctopon
    cfv
    #
    @26
    wph
    @3
    cvv
    wcel
    #
    @4
    @28
    wcel
    wph
    cR
    ctsr
    wcel
    #
    @29
    ordtrest2.2
    cR
    @2
    ctsr
    inex1g
    syl
    #
    @3
    cvv
    @27
    @27
    eqid
    #
    ordttopon
    syl
    wph
    @27
    cA
    ctopon
    wph
    cR
    cps
    wcel
    #
    @22
    @27
    cA
    wceq
    #
    wph
    @30
    @33
    ordtrest2.2
    cR
    tsrps
    syl
    ordtrest2.3
    cA
    cR
    cX
    ordtrest2.1
    psssdm
    syl2anc
    #
    fveq2d
    eleqtrd
    cA
    @4
    toponmax
    syl
    adantr
    @23
    cA
    @18
    wceq
    @25
    @24
    wb
    @9
    vw
    cA
    rabid2
    cA
    @18
    @4
    eleq1
    sylbir
    syl5ibcom
    @23
    wn
    #
    vx
    cv
    #
    @7
    cR
    wbr
    #
    vx
    cA
    wrex
    #
    @17
    @24
    @36
    @8
    vw
    cA
    wrex
    @39
    @8
    vw
    cA
    dfrex2
    @8
    @38
    vw
    vx
    cA
    @6
    @37
    @7
    cR
    breq1
    cbvrexv
    bitr3i
    @17
    @38
    @24
    vx
    cA
    @17
    @37
    cA
    wcel
    #
    @38
    wa
    #
    wa
    #
    @24
    @18
    c0
    @42
    @24
    @18
    c0
    wceq
    c0
    @4
    wcel
    #
    @17
    @43
    @41
    @17
    @4
    ctop
    wcel
    #
    @43
    wph
    @44
    @16
    wph
    @29
    @44
    @31
    @3
    cvv
    ordttop
    syl
    adantr
    @4
    0opn
    syl
    adantr
    @18
    c0
    @4
    eleq1
    syl5ibrcom
    @18
    c0
    wne
    #
    vy
    cv
    #
    @7
    cR
    wbr
    #
    wn
    #
    vy
    cA
    wrex
    #
    @42
    @24
    @45
    @9
    vw
    cA
    wrex
    @49
    @9
    vw
    cA
    rabn0
    @9
    @48
    vw
    vy
    cA
    @6
    @46
    wceq
    @8
    @47
    @6
    @46
    @7
    cR
    breq1
    notbid
    cbvrexv
    bitri
    @42
    @48
    @24
    vy
    cA
    @42
    @46
    cA
    wcel
    #
    wa
    #
    @48
    @7
    @46
    cR
    wbr
    #
    @24
    @51
    @47
    @52
    @51
    @30
    @46
    cX
    wcel
    @16
    @47
    @52
    wo
    wph
    @30
    @16
    @41
    @50
    ordtrest2.2
    ad3antrrr
    @42
    cA
    cX
    @46
    wph
    @22
    @16
    @41
    ordtrest2.3
    ad2antrr
    sselda
    wph
    @16
    @41
    @50
    simpllr
    @46
    @7
    cR
    cX
    ordtrest2.1
    tsrlin
    syl3anc
    ord
    @42
    @50
    @52
    @24
    @17
    @41
    @50
    @52
    wa
    #
    @24
    @17
    @41
    @53
    wa
    #
    wa
    #
    @18
    @6
    @7
    @3
    wbr
    #
    wn
    #
    vw
    @27
    crab
    #
    @4
    @55
    @18
    @57
    vw
    cA
    crab
    #
    @58
    @55
    @7
    cA
    wcel
    #
    @18
    @59
    wceq
    @54
    @17
    @40
    @50
    wa
    #
    @38
    @52
    wa
    #
    wa
    @60
    @40
    @38
    @50
    @52
    an4
    @17
    @61
    @62
    @60
    wph
    @61
    @16
    @62
    @60
    wi
    #
    wph
    @61
    wa
    #
    @63
    vz
    cX
    @64
    @62
    vz
    cX
    crab
    cA
    wss
    @63
    vz
    cX
    wral
    ordtrest2.4
    @62
    vz
    cX
    cA
    rabss
    sylib
    r19.21bi
    an32s
    impr
    sylan2b
    #
    @60
    @9
    @57
    vw
    cA
    @60
    @6
    cA
    wcel
    #
    wa
    @8
    @56
    @66
    @60
    @8
    @56
    wb
    @6
    @7
    cA
    cA
    cR
    brinxp
    ancoms
    notbid
    rabbidva
    syl
    @55
    @34
    @58
    @59
    wceq
    wph
    @34
    @16
    @54
    @35
    ad2antrr
    #
    @57
    vw
    @27
    cA
    rabeq
    syl
    eqtr4d
    @55
    @29
    @7
    @27
    wcel
    @58
    @4
    wcel
    wph
    @29
    @16
    @54
    @31
    ad2antrr
    @55
    @7
    cA
    @27
    @65
    @67
    eleqtrrd
    vw
    @7
    @3
    cvv
    @27
    @32
    ordtopn1
    syl2anc
    eqeltrd
    anassrs
    expr
    syld
    rexlimdva
    syl5bi
    pm2.61dne
    rexlimdvaa
    syl5bi
    pm2.61d
    eqeltrd
    ralrimiva
    wph
    @10
    cvv
    wcel
    #
    vz
    cX
    wral
    @12
    @15
    wb
    wph
    @68
    vz
    cX
    wph
    cX
    cvv
    wcel
    @68
    wph
    cX
    cR
    cdm
    #
    cvv
    ordtrest2.1
    wph
    @30
    @69
    cvv
    wcel
    ordtrest2.2
    cR
    ctsr
    dmexg
    syl
    syl5eqel
    @9
    vw
    cX
    cvv
    rabexg
    syl
    ralrimivw
    @5
    @14
    vz
    vv
    cX
    @10
    @11
    cvv
    @11
    eqid
    @0
    @10
    wceq
    @1
    @13
    @4
    @0
    @10
    cA
    ineq1
    eleq1d
    ralrnmpt
    syl
    mpbird
end
