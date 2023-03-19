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
include "cple.mm"
include "fvex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "a1i.mm"
include "eqid.mm"
include "ordttopon.mm"
include "cpreset.mm"
include "ctos.mm"
include "cpo.mm"
include "tospos.mm"
include "posprs.mm"
include "3syl.mm"
include "prsssdm.mm"
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
include "trleile.mm"
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
include "cbs.mm"
include "rabexg.mm"
include "ralrimivw.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ralrnmpt.mm"
include "mpbird.mm"

theorem ordtrest2NEWlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )
  assume ordtrest2NEW.2: |- ( ph -> K e. Toset )
  assume ordtrest2NEW.3: |- ( ph -> A C_ B )
  assume ordtrest2NEW.4: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> { z e. B | ( x .<_ z /\ z .<_ y ) } C_ A )

  disjoint x y
  disjoint .<_ x
  disjoint .<_ y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint A x
  disjoint A y
  disjoint v x
  disjoint v y
  disjoint v w
  disjoint v z
  disjoint .<_ v
  disjoint w x
  disjoint x z
  disjoint w y
  disjoint y z
  disjoint w z
  disjoint .<_ w
  disjoint .<_ z
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint B v
  disjoint B w
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> A. v e. ran ( z e. B |-> { w e. B | -. w .<_ z } ) ( v i^i A ) e. ( ordTop ` ( .<_ i^i ( A X. A ) ) ) )

  proof
    wph
    vv
    cv
    #
    cA
    cin
    #
    c.le
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
    cB
    vw
    cv
    #
    vz
    cv
    #
    c.le
    wbr
    #
    wn
    #
    vw
    cB
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
    cB
    wral
    #
    wph
    @14
    vz
    cB
    wph
    @7
    cB
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
    cB
    cA
    cin
    #
    crab
    #
    @18
    @9
    vw
    cB
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
    cB
    wss
    #
    @21
    ordtrest2NEW.3
    cA
    cB
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
    @29
    wph
    c.le
    @2
    c.le
    cK
    cple
    cfv
    #
    cB
    cB
    cxp
    #
    cin
    cvv
    ordtNEW.l
    @30
    @31
    cK
    cple
    fvex
    inex1
    eqeltri
    inex1
    #
    a1i
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
    cK
    cpreset
    wcel
    #
    @22
    @27
    cA
    wceq
    #
    wph
    cK
    ctos
    wcel
    #
    cK
    cpo
    wcel
    @35
    ordtrest2NEW.2
    cK
    tospos
    cK
    posprs
    3syl
    ordtrest2NEW.3
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsssdm
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
    c.le
    wbr
    #
    vx
    cA
    wrex
    #
    @17
    @24
    @39
    @8
    vw
    cA
    wrex
    @42
    @8
    vw
    cA
    dfrex2
    @8
    @41
    vw
    vx
    cA
    @6
    @40
    @7
    c.le
    breq1
    cbvrexv
    bitr3i
    @17
    @41
    @24
    vx
    cA
    @17
    @40
    cA
    wcel
    #
    @41
    wa
    #
    wa
    #
    @24
    @18
    c0
    @45
    @24
    @18
    c0
    wceq
    c0
    @4
    wcel
    #
    @17
    @46
    @44
    @17
    @4
    ctop
    wcel
    #
    @46
    wph
    @47
    @16
    wph
    @29
    @47
    @33
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
    c.le
    wbr
    #
    wn
    #
    vy
    cA
    wrex
    #
    @45
    @24
    @48
    @9
    vw
    cA
    wrex
    @52
    @9
    vw
    cA
    rabn0
    @9
    @51
    vw
    vy
    cA
    @6
    @49
    wceq
    @8
    @50
    @6
    @49
    @7
    c.le
    breq1
    notbid
    cbvrexv
    bitri
    @45
    @51
    @24
    vy
    cA
    @45
    @49
    cA
    wcel
    #
    wa
    #
    @51
    @7
    @49
    c.le
    wbr
    #
    @24
    @54
    @50
    @55
    @54
    @37
    @49
    cB
    wcel
    @16
    @50
    @55
    wo
    wph
    @37
    @16
    @44
    @53
    ordtrest2NEW.2
    ad3antrrr
    @45
    cA
    cB
    @49
    wph
    @22
    @16
    @44
    ordtrest2NEW.3
    ad2antrr
    sselda
    wph
    @16
    @44
    @53
    simpllr
    cB
    cK
    c.le
    @49
    @7
    ordtNEW.b
    ordtNEW.l
    trleile
    syl3anc
    ord
    @45
    @53
    @55
    @24
    @17
    @44
    @53
    @55
    wa
    #
    @24
    @17
    @44
    @56
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
    @58
    @18
    @60
    vw
    cA
    crab
    #
    @61
    @58
    @7
    cA
    wcel
    #
    @18
    @62
    wceq
    @57
    @17
    @43
    @53
    wa
    #
    @41
    @55
    wa
    #
    wa
    @63
    @43
    @41
    @53
    @55
    an4
    @17
    @64
    @65
    @63
    wph
    @64
    @16
    @65
    @63
    wi
    #
    wph
    @64
    wa
    #
    @66
    vz
    cB
    @67
    @65
    vz
    cB
    crab
    cA
    wss
    @66
    vz
    cB
    wral
    ordtrest2NEW.4
    @65
    vz
    cB
    cA
    rabss
    sylib
    r19.21bi
    an32s
    impr
    sylan2b
    #
    @63
    @9
    @60
    vw
    cA
    @63
    @6
    cA
    wcel
    #
    wa
    @8
    @59
    @69
    @63
    @8
    @59
    wb
    @6
    @7
    cA
    cA
    c.le
    brinxp
    ancoms
    notbid
    rabbidva
    syl
    @58
    @36
    @61
    @62
    wceq
    wph
    @36
    @16
    @57
    @38
    ad2antrr
    #
    @60
    vw
    @27
    cA
    rabeq
    syl
    eqtr4d
    @58
    @29
    @7
    @27
    wcel
    @61
    @4
    wcel
    @29
    @58
    @32
    a1i
    @58
    @7
    cA
    @27
    @68
    @70
    eleqtrrd
    vw
    @7
    @3
    cvv
    @27
    @34
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
    cB
    wral
    @12
    @15
    wb
    wph
    @71
    vz
    cB
    wph
    cB
    cvv
    wcel
    #
    @71
    @72
    wph
    cB
    cK
    cbs
    cfv
    cvv
    ordtNEW.b
    cK
    cbs
    fvex
    eqeltri
    a1i
    @9
    vw
    cB
    cvv
    rabexg
    syl
    ralrimivw
    @5
    @14
    vz
    vv
    cB
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
