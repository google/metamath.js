include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "cpreset.mm"
include "wcel.mm"
include "wss.mm"
include "ctos.mm"
include "cpo.mm"
include "tospos.mm"
include "posprs.mm"
include "3syl.mm"
include "ordtrestNEW.mm"
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
include "ordtprsval.mm"
include "syl.mm"
include "oveq1d.mm"
include "ctb.mm"
include "cvv.mm"
include "fibas.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ssexd.mm"
include "tgrest.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "firest.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "ctop.mm"
include "cple.mm"
include "inex1.mm"
include "ordttop.mm"
include "mp1i.mm"
include "cuni.mm"
include "ordtprsuni.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "restval.mm"
include "wf.mm"
include "wral.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ctopon.mm"
include "cdm.mm"
include "ordttopon.mm"
include "prsssdm.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "toponmax.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "ineq1d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "ralrimiv.mm"
include "ordtrest2NEWlem.mm"
include "ccnv.mm"
include "codu.mm"
include "odubas.mm"
include "cnveqi.mm"
include "cnvin.mm"
include "cnvxp.mm"
include "ineq2i.mm"
include "oduleval.mm"
include "ineq1i.mm"
include "3eqtri.mm"
include "eqtri.mm"
include "odutos.mm"
include "wa.mm"
include "vex.mm"
include "brcnv.mm"
include "anbi12ci.mm"
include "rabbii.mm"
include "syl5eqss.mm"
include "ancom2s.mm"
include "wb.mm"
include "bicomi.mm"
include "notbid.mm"
include "rabbidv.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "cress.mm"
include "ressprs.mm"
include "ordtcnvNEW.mm"
include "prsss.mm"
include "ressle.mm"
include "ressbas2.mm"
include "sqxpeqd.mm"
include "ineq12d.mm"
include "eqtrd.mm"
include "cnveqd.mm"
include "3eqtr4d.mm"
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

theorem ordtrest2NEW
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vv: setvar v
  let vw: setvar w
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
  disjoint x z
  disjoint y z
  disjoint .<_ z
  disjoint A z
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K z
  disjoint v x
  disjoint v y
  disjoint v w
  disjoint v z
  disjoint .<_ v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .<_ w
  disjoint A v
  disjoint A w
  disjoint B v
  disjoint B w
  disjoint K w
  disjoint ph v
  disjoint ph w
  assert |- ( ph -> ( ordTop ` ( .<_ i^i ( A X. A ) ) ) = ( ( ordTop ` .<_ ) |`t A ) )

  proof
    wph
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
    c.le
    cordt
    cfv
    #
    cA
    crest
    co
    #
    wph
    cK
    cpreset
    wcel
    #
    cA
    cB
    wss
    #
    @2
    @4
    wss
    wph
    cK
    ctos
    wcel
    #
    cK
    cpo
    wcel
    @5
    ordtrest2NEW.2
    cK
    tospos
    cK
    posprs
    3syl
    #
    ordtrest2NEW.3
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    ordtrestNEW
    syl2anc
    wph
    @4
    cB
    csn
    #
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
    wn
    vw
    cB
    crab
    cmpt
    crn
    #
    vz
    cB
    @11
    @10
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
    @19
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
    @22
    wph
    @4
    @23
    ctg
    cfv
    #
    cA
    crest
    co
    #
    @25
    wph
    @3
    @26
    cA
    crest
    wph
    @5
    @3
    @26
    wceq
    @8
    vz
    vw
    cB
    @12
    @17
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    @12
    eqid
    #
    @17
    eqid
    #
    ordtprsval
    syl
    oveq1d
    wph
    @23
    ctb
    wcel
    cA
    cvv
    wcel
    #
    @25
    @27
    wceq
    @19
    fibas
    wph
    cA
    cB
    cvv
    cB
    cvv
    wcel
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
    #
    ordtrest2NEW.3
    ssexd
    #
    cA
    @23
    ctb
    cvv
    tgrest
    sylancr
    eqtr4d
    @21
    @24
    ctg
    cA
    @19
    firest
    fveq2i
    syl6eqr
    wph
    @2
    ctop
    wcel
    #
    @20
    @2
    wss
    @22
    @2
    wss
    @1
    cvv
    wcel
    #
    @33
    wph
    c.le
    @0
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
    #
    cvv
    ordtNEW.l
    @35
    @36
    cK
    cple
    fvex
    inex1
    eqeltri
    inex1
    #
    @1
    cvv
    ordttop
    mp1i
    wph
    @20
    vv
    @19
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
    @19
    cvv
    wcel
    #
    @30
    @20
    @42
    wceq
    wph
    @19
    cuni
    #
    cvv
    wcel
    @43
    wph
    cB
    @44
    cvv
    wph
    @5
    cB
    @44
    wceq
    @8
    vz
    vw
    cB
    @12
    @17
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    @28
    @29
    ordtprsuni
    syl
    @31
    eqeltrrd
    @19
    uniexb
    sylibr
    @32
    vv
    cA
    @19
    cvv
    cvv
    restval
    syl2anc
    wph
    @19
    @2
    @41
    wf
    #
    @42
    @2
    wss
    wph
    @40
    @2
    wcel
    #
    vv
    @19
    wral
    #
    @45
    wph
    @46
    vv
    @9
    wral
    @46
    vv
    @18
    wral
    #
    @47
    wph
    @46
    vv
    @9
    wph
    @46
    @39
    @9
    wcel
    #
    cB
    cA
    cin
    #
    @2
    wcel
    wph
    @50
    cA
    @2
    wph
    @6
    @50
    cA
    wceq
    ordtrest2NEW.3
    cA
    cB
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
    @51
    @34
    @2
    @53
    wcel
    wph
    @38
    @1
    cvv
    @52
    @52
    eqid
    ordttopon
    mp1i
    wph
    @52
    cA
    ctopon
    wph
    @5
    @6
    @52
    cA
    wceq
    @8
    ordtrest2NEW.3
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsssdm
    syl2anc
    fveq2d
    eleqtrd
    cA
    @2
    toponmax
    syl
    eqeltrd
    @49
    @40
    @50
    @2
    @49
    @39
    cB
    cA
    @39
    cB
    elsni
    ineq1d
    eleq1d
    syl5ibrcom
    ralrimiv
    wph
    @46
    vv
    @12
    wral
    @46
    vv
    @17
    wral
    #
    @48
    wph
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    ordtrest2NEW.2
    ordtrest2NEW.3
    ordtrest2NEW.4
    ordtrest2NEWlem
    wph
    @54
    @40
    c.le
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
    cB
    @10
    @11
    @55
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
    #
    wral
    wph
    vy
    vx
    vz
    vw
    vv
    cA
    cB
    cK
    codu
    cfv
    #
    @55
    cB
    @64
    cK
    @64
    eqid
    #
    ordtNEW.b
    odubas
    @55
    @37
    ccnv
    #
    @64
    cple
    cfv
    #
    @36
    cin
    #
    c.le
    @37
    ordtNEW.l
    cnveqi
    @66
    @35
    ccnv
    #
    @36
    ccnv
    #
    cin
    @69
    @36
    cin
    @68
    @35
    @36
    cnvin
    @70
    @36
    @69
    cB
    cB
    cnvxp
    ineq2i
    @69
    @67
    @36
    @64
    @35
    cK
    @65
    @35
    eqid
    #
    oduleval
    ineq1i
    3eqtri
    eqtri
    wph
    @7
    @64
    ctos
    wcel
    ordtrest2NEW.2
    @64
    cK
    @65
    odutos
    syl
    ordtrest2NEW.3
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
    @74
    @11
    @55
    wbr
    #
    @11
    @72
    @55
    wbr
    #
    wa
    #
    vz
    cB
    crab
    #
    cA
    wss
    wph
    @73
    @75
    wa
    wa
    @79
    @72
    @11
    c.le
    wbr
    #
    @11
    @74
    c.le
    wbr
    #
    wa
    #
    vz
    cB
    crab
    cA
    @78
    @82
    vz
    cB
    @76
    @81
    @77
    @80
    @74
    @11
    c.le
    vy
    vex
    vz
    vex
    #
    brcnv
    @11
    @72
    c.le
    @83
    vx
    vex
    brcnv
    anbi12ci
    rabbii
    ordtrest2NEW.4
    syl5eqss
    ancom2s
    ordtrest2NEWlem
    wph
    @46
    @58
    vv
    @17
    @63
    wph
    @16
    @62
    wph
    vz
    cB
    @15
    @61
    wph
    @14
    @60
    vw
    cB
    wph
    @13
    @59
    @13
    @59
    wb
    wph
    @59
    @13
    @10
    @11
    c.le
    vw
    vex
    @83
    brcnv
    bicomi
    a1i
    notbid
    rabbidv
    mpteq2dv
    rneqd
    wph
    @2
    @57
    @40
    wph
    @57
    @1
    ccnv
    #
    cordt
    cfv
    #
    @2
    @84
    @56
    cordt
    @84
    @55
    @0
    ccnv
    #
    cin
    @56
    c.le
    @0
    cnvin
    @86
    @0
    @55
    cA
    cA
    cnvxp
    ineq2i
    eqtri
    fveq2i
    wph
    cK
    cA
    cress
    co
    #
    cple
    cfv
    #
    @87
    cbs
    cfv
    #
    @89
    cxp
    #
    cin
    #
    ccnv
    #
    cordt
    cfv
    #
    @91
    cordt
    cfv
    #
    @85
    @2
    wph
    @87
    cpreset
    wcel
    #
    @93
    @94
    wceq
    wph
    @5
    @6
    @95
    @8
    ordtrest2NEW.3
    cA
    cB
    cK
    ordtNEW.b
    ressprs
    syl2anc
    @89
    @87
    @91
    @89
    eqid
    @91
    eqid
    ordtcnvNEW
    syl
    wph
    @84
    @92
    cordt
    wph
    @1
    @91
    wph
    @1
    @35
    @0
    cin
    #
    @91
    wph
    @5
    @6
    @1
    @96
    wceq
    @8
    ordtrest2NEW.3
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsss
    syl2anc
    wph
    @35
    @88
    @0
    @90
    wph
    @30
    @35
    @88
    wceq
    @32
    cA
    cK
    @35
    cvv
    @87
    @87
    eqid
    #
    @71
    ressle
    syl
    wph
    cA
    @89
    wph
    @6
    cA
    @89
    wceq
    ordtrest2NEW.3
    cA
    cB
    @87
    cK
    @97
    ordtNEW.b
    ressbas2
    syl
    sqxpeqd
    ineq12d
    eqtrd
    #
    cnveqd
    fveq2d
    wph
    @1
    @91
    cordt
    @98
    fveq2d
    3eqtr4d
    syl5reqr
    eleq2d
    raleqbidv
    mpbird
    @46
    vv
    @12
    @17
    ralunb
    sylanbrc
    @46
    vv
    @9
    @18
    ralunb
    sylanbrc
    vv
    @19
    @2
    @40
    @41
    @41
    eqid
    fmpt
    sylib
    @19
    @2
    @41
    frn
    syl
    eqsstrd
    @20
    @2
    tgfiss
    syl2anc
    eqsstrd
    eqssd
end
