include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cps.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "ctsr.mm"
include "tsrps.mm"
include "syl.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "ssexd.mm"
include "ordtrest.mm"
include "syl2anc.mm"
include "csn.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "ctg.mm"
include "wceq.mm"
include "eqid.mm"
include "ordtval.mm"
include "oveq1d.mm"
include "ctb.mm"
include "fibas.mm"
include "tgrest.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "firest.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "ctop.mm"
include "inex1g.mm"
include "ordttop.mm"
include "cuni.mm"
include "ordtuni.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "restval.mm"
include "wf.mm"
include "wral.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ctopon.mm"
include "ordttopon.mm"
include "psssdm.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "toponmax.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "ineq1d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ordtrest2lem.mm"
include "ccnv.mm"
include "df-rn.mm"
include "cnvtsr.mm"
include "psrn.mm"
include "sseqtrd.mm"
include "wa.mm"
include "adantr.mm"
include "rabeq.mm"
include "vex.mm"
include "brcnv.mm"
include "anbi12ci.mm"
include "rabbii.mm"
include "eqsstr3d.mm"
include "ancom2s.mm"
include "wb.mm"
include "bicomi.mm"
include "a1i.mm"
include "notbid.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "cnvin.mm"
include "cnvxp.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "psss.mm"
include "ordtcnv.mm"
include "syl5reqr.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "mpbird.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "fmpt.mm"
include "frn.mm"
include "eqsstrd.mm"
include "tgfiss.mm"
include "eqssd.mm"

theorem ordtrest2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cX: class X
  let vv: setvar v
  let vw: setvar w
  let cV: class V
  assume ordtrest2.1: |- X = dom R
  assume ordtrest2.2: |- ( ph -> R e. TosetRel )
  assume ordtrest2.3: |- ( ph -> A C_ X )
  assume ordtrest2.4: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> { z e. X | ( x R z /\ z R y ) } C_ A )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint ph v
  disjoint ph w
  disjoint R v
  disjoint R w
  disjoint X v
  disjoint X w
  disjoint V x
  disjoint V y
  assert |- ( ph -> ( ordTop ` ( R i^i ( A X. A ) ) ) = ( ( ordTop ` R ) |`t A ) )

  proof
    wph
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
    cR
    cordt
    cfv
    #
    cA
    crest
    co
    #
    wph
    cR
    cps
    wcel
    #
    cA
    cvv
    wcel
    #
    @2
    @4
    wss
    wph
    cR
    ctsr
    wcel
    #
    @5
    ordtrest2.2
    cR
    tsrps
    syl
    #
    wph
    cA
    cX
    cvv
    wph
    cX
    cR
    cdm
    #
    cvv
    ordtrest2.1
    wph
    @7
    @9
    cvv
    wcel
    ordtrest2.2
    cR
    ctsr
    dmexg
    syl
    syl5eqel
    #
    ordtrest2.3
    ssexd
    #
    cA
    cR
    cvv
    ordtrest
    syl2anc
    wph
    @4
    cX
    csn
    #
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
    wn
    vw
    cX
    crab
    cmpt
    crn
    #
    vz
    cX
    @14
    @13
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
    #
    cun
    #
    cun
    #
    cA
    crest
    co
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    @2
    wph
    @4
    @22
    cfi
    cfv
    #
    cA
    crest
    co
    #
    ctg
    cfv
    #
    @25
    wph
    @4
    @26
    ctg
    cfv
    #
    cA
    crest
    co
    #
    @28
    wph
    @3
    @29
    cA
    crest
    wph
    @7
    @3
    @29
    wceq
    ordtrest2.2
    vz
    vw
    @15
    @20
    cR
    ctsr
    cX
    ordtrest2.1
    @15
    eqid
    #
    @20
    eqid
    #
    ordtval
    syl
    oveq1d
    wph
    @26
    ctb
    wcel
    @6
    @28
    @30
    wceq
    @22
    fibas
    @11
    cA
    @26
    ctb
    cvv
    tgrest
    sylancr
    eqtr4d
    @24
    @27
    ctg
    cA
    @22
    firest
    fveq2i
    syl6eqr
    wph
    @2
    ctop
    wcel
    #
    @23
    @2
    wss
    @25
    @2
    wss
    wph
    @1
    cvv
    wcel
    #
    @33
    wph
    @7
    @34
    ordtrest2.2
    cR
    @0
    ctsr
    inex1g
    syl
    #
    @1
    cvv
    ordttop
    syl
    wph
    @23
    vv
    @22
    vv
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    @2
    wph
    @22
    cvv
    wcel
    #
    @6
    @23
    @39
    wceq
    wph
    @22
    cuni
    #
    cvv
    wcel
    @40
    wph
    cX
    @41
    cvv
    wph
    @7
    cX
    @41
    wceq
    ordtrest2.2
    vz
    vw
    @15
    @20
    cR
    ctsr
    cX
    ordtrest2.1
    @31
    @32
    ordtuni
    syl
    @10
    eqeltrrd
    @22
    uniexb
    sylibr
    @11
    vv
    cA
    @22
    cvv
    cvv
    restval
    syl2anc
    wph
    @22
    @2
    @38
    wf
    #
    @39
    @2
    wss
    wph
    @37
    @2
    wcel
    #
    vv
    @22
    wral
    #
    @42
    wph
    @43
    vv
    @12
    wral
    @43
    vv
    @21
    wral
    #
    @44
    wph
    @43
    vv
    @12
    wph
    @43
    @36
    @12
    wcel
    #
    cX
    cA
    cin
    #
    @2
    wcel
    wph
    @47
    cA
    @2
    wph
    cA
    cX
    wss
    #
    @47
    cA
    wceq
    ordtrest2.3
    cA
    cX
    sseqin2
    sylib
    wph
    @2
    cA
    ctopon
    cfv
    #
    wcel
    cA
    @2
    wcel
    wph
    @2
    @1
    cdm
    #
    ctopon
    cfv
    #
    @49
    wph
    @34
    @2
    @51
    wcel
    @35
    @1
    cvv
    @50
    @50
    eqid
    ordttopon
    syl
    wph
    @50
    cA
    ctopon
    wph
    @5
    @48
    @50
    cA
    wceq
    @8
    ordtrest2.3
    cA
    cR
    cX
    ordtrest2.1
    psssdm
    syl2anc
    fveq2d
    eleqtrd
    cA
    @2
    toponmax
    syl
    eqeltrd
    @46
    @37
    @47
    @2
    @46
    @36
    cX
    cA
    @36
    cX
    elsni
    ineq1d
    eleq1d
    syl5ibrcom
    ralrimiv
    wph
    @43
    vv
    @15
    wral
    @43
    vv
    @20
    wral
    #
    @45
    wph
    vx
    vy
    vz
    vw
    vv
    cA
    cR
    cX
    ordtrest2.1
    ordtrest2.2
    ordtrest2.3
    ordtrest2.4
    ordtrest2lem
    wph
    @52
    @37
    cR
    ccnv
    #
    @0
    cin
    #
    cordt
    cfv
    #
    wcel
    #
    vv
    vz
    cR
    crn
    #
    @13
    @14
    @53
    wbr
    #
    wn
    #
    vw
    @57
    crab
    #
    cmpt
    #
    crn
    #
    wral
    wph
    vy
    vx
    vz
    vw
    vv
    cA
    @53
    @57
    cR
    df-rn
    wph
    @7
    @53
    ctsr
    wcel
    ordtrest2.2
    cR
    cnvtsr
    syl
    wph
    cA
    cX
    @57
    ordtrest2.3
    wph
    @5
    cX
    @57
    wceq
    #
    @8
    cR
    cX
    ordtrest2.1
    psrn
    syl
    #
    sseqtrd
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    @67
    @14
    @53
    wbr
    #
    @14
    @65
    @53
    wbr
    #
    wa
    #
    vz
    @57
    crab
    #
    cA
    wss
    wph
    @66
    @68
    wa
    #
    wa
    #
    @72
    @65
    @14
    cR
    wbr
    #
    @14
    @67
    cR
    wbr
    #
    wa
    #
    vz
    cX
    crab
    #
    cA
    @74
    @78
    @77
    vz
    @57
    crab
    #
    @72
    @74
    @63
    @78
    @79
    wceq
    wph
    @63
    @73
    @64
    adantr
    @77
    vz
    cX
    @57
    rabeq
    syl
    @71
    @77
    vz
    @57
    @69
    @76
    @70
    @75
    @67
    @14
    cR
    vy
    vex
    vz
    vex
    #
    brcnv
    @14
    @65
    cR
    @80
    vx
    vex
    brcnv
    anbi12ci
    rabbii
    syl6eqr
    ordtrest2.4
    eqsstr3d
    ancom2s
    ordtrest2lem
    wph
    @43
    @56
    vv
    @20
    @62
    wph
    @19
    @61
    wph
    vz
    cX
    @18
    @57
    @60
    @64
    wph
    @17
    @59
    vw
    cX
    @57
    @64
    wph
    @16
    @58
    @16
    @58
    wb
    wph
    @58
    @16
    @13
    @14
    cR
    vw
    vex
    @80
    brcnv
    bicomi
    a1i
    notbid
    rabeqbidv
    mpteq12dv
    rneqd
    wph
    @2
    @55
    @37
    wph
    @55
    @1
    ccnv
    #
    cordt
    cfv
    #
    @2
    @81
    @54
    cordt
    @81
    @53
    @0
    ccnv
    #
    cin
    @54
    cR
    @0
    cnvin
    @83
    @0
    @53
    cA
    cA
    cnvxp
    ineq2i
    eqtri
    fveq2i
    wph
    @1
    cps
    wcel
    #
    @82
    @2
    wceq
    wph
    @5
    @84
    @8
    cA
    cR
    psss
    syl
    @1
    ordtcnv
    syl
    syl5reqr
    eleq2d
    raleqbidv
    mpbird
    @43
    vv
    @15
    @20
    ralunb
    sylanbrc
    @43
    vv
    @12
    @21
    ralunb
    sylanbrc
    vv
    @22
    @2
    @37
    @38
    @38
    eqid
    fmpt
    sylib
    @22
    @2
    @38
    frn
    syl
    eqsstrd
    @23
    @2
    tgfiss
    syl2anc
    eqsstrd
    eqssd
end
