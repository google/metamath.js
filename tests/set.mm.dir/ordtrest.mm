include "cps.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "cdm.mm"
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
include "crest.mm"
include "co.mm"
include "cvv.mm"
include "wceq.mm"
include "inex1g.mm"
include "adantr.mm"
include "eqid.mm"
include "ordtval.mm"
include "syl.mm"
include "ctop.mm"
include "wss.mm"
include "ordttop.mm"
include "resttop.mm"
include "sylan.mm"
include "psssdm2.mm"
include "simpr.mm"
include "ctopon.mm"
include "ordttopon.mm"
include "toponmax.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "snssd.mm"
include "rabeq.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "wf.mm"
include "inrab2.mm"
include "wb.mm"
include "inss2.mm"
include "sseldi.mm"
include "brinxp.mm"
include "syl2anc.mm"
include "notbid.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "simpl.mm"
include "inss1.mm"
include "sseli.mm"
include "ordtopn1.mm"
include "syl2an.mm"
include "eqeltrrd.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "ordtopn2.mm"
include "unssd.mm"
include "tgfiss.mm"

theorem ordtrest
  let cA: class A
  let cR: class R
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let cX: class X


  assert |- ( ( R e. PosetRel /\ A e. V ) -> ( ordTop ` ( R i^i ( A X. A ) ) ) C_ ( ( ordTop ` R ) |`t A ) )

  proof
    cR
    cps
    wcel
    #
    cA
    cV
    wcel
    #
    wa
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
    @4
    cdm
    #
    csn
    #
    vx
    @6
    vy
    cv
    #
    vx
    cv
    #
    @4
    wbr
    #
    wn
    #
    vy
    @6
    crab
    #
    cmpt
    #
    crn
    #
    vx
    @6
    @9
    @8
    @4
    wbr
    #
    wn
    #
    vy
    @6
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
    cfi
    cfv
    ctg
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
    @2
    @4
    cvv
    wcel
    #
    @5
    @22
    wceq
    @0
    @25
    @1
    cR
    @3
    cps
    inex1g
    adantr
    vx
    vy
    @14
    @19
    @4
    cvv
    @6
    @6
    eqid
    @14
    eqid
    @19
    eqid
    ordtval
    syl
    @2
    @24
    ctop
    wcel
    #
    @21
    @24
    wss
    @22
    @24
    wss
    @0
    @23
    ctop
    wcel
    #
    @1
    @26
    cR
    cps
    ordttop
    #
    cA
    @23
    cV
    resttop
    sylan
    @2
    @7
    @20
    @24
    @2
    @6
    @24
    @2
    @6
    cR
    cdm
    #
    cA
    cin
    #
    @24
    @0
    @6
    @30
    wceq
    #
    @1
    cA
    cR
    @29
    @29
    eqid
    #
    psssdm2
    adantr
    #
    @2
    @27
    @1
    @29
    @23
    wcel
    #
    @30
    @24
    wcel
    @0
    @27
    @1
    @28
    adantr
    #
    @0
    @1
    simpr
    #
    @2
    @23
    @29
    ctopon
    cfv
    wcel
    #
    @34
    @0
    @37
    @1
    cR
    cps
    @29
    @32
    ordttopon
    adantr
    @29
    @23
    toponmax
    syl
    @29
    cA
    @23
    ctop
    cV
    elrestr
    syl3anc
    eqeltrd
    snssd
    @2
    @14
    @19
    @24
    @2
    @14
    vx
    @30
    @11
    vy
    @30
    crab
    #
    cmpt
    #
    crn
    #
    @24
    @2
    @13
    @39
    @2
    vx
    @6
    @12
    @30
    @38
    @33
    @2
    @31
    @12
    @38
    wceq
    @33
    @11
    vy
    @6
    @30
    rabeq
    syl
    mpteq12dv
    rneqd
    @2
    @30
    @24
    @39
    wf
    @40
    @24
    wss
    @2
    vx
    @30
    @38
    @24
    @39
    @2
    @9
    @30
    wcel
    #
    wa
    #
    @8
    @9
    cR
    wbr
    #
    wn
    #
    vy
    @29
    crab
    #
    cA
    cin
    #
    @38
    @24
    @42
    @46
    @44
    vy
    @30
    crab
    @38
    @44
    vy
    @29
    cA
    inrab2
    @42
    @44
    @11
    vy
    @30
    @42
    @8
    @30
    wcel
    #
    wa
    #
    @43
    @10
    @48
    @8
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    @43
    @10
    wb
    @48
    @30
    cA
    @8
    @29
    cA
    inss2
    #
    @42
    @47
    simpr
    sseldi
    #
    @42
    @50
    @47
    @42
    @30
    cA
    @9
    @51
    @2
    @41
    simpr
    sseldi
    adantr
    #
    @8
    @9
    cA
    cA
    cR
    brinxp
    syl2anc
    notbid
    rabbidva
    syl5eq
    @42
    @27
    @1
    @45
    @23
    wcel
    #
    @46
    @24
    wcel
    @2
    @27
    @41
    @35
    adantr
    #
    @2
    @1
    @41
    @36
    adantr
    #
    @2
    @0
    @9
    @29
    wcel
    #
    @54
    @41
    @0
    @1
    simpl
    #
    @30
    @29
    @9
    @29
    cA
    inss1
    sseli
    #
    vy
    @9
    cR
    cps
    @29
    @32
    ordtopn1
    syl2an
    @45
    cA
    @23
    ctop
    cV
    elrestr
    syl3anc
    eqeltrrd
    @39
    eqid
    fmptd
    @30
    @24
    @39
    frn
    syl
    eqsstrd
    @2
    @19
    vx
    @30
    @16
    vy
    @30
    crab
    #
    cmpt
    #
    crn
    #
    @24
    @2
    @18
    @61
    @2
    vx
    @6
    @17
    @30
    @60
    @33
    @2
    @31
    @17
    @60
    wceq
    @33
    @16
    vy
    @6
    @30
    rabeq
    syl
    mpteq12dv
    rneqd
    @2
    @30
    @24
    @61
    wf
    @62
    @24
    wss
    @2
    vx
    @30
    @60
    @24
    @61
    @42
    @9
    @8
    cR
    wbr
    #
    wn
    #
    vy
    @29
    crab
    #
    cA
    cin
    #
    @60
    @24
    @42
    @66
    @64
    vy
    @30
    crab
    @60
    @64
    vy
    @29
    cA
    inrab2
    @42
    @64
    @16
    vy
    @30
    @48
    @63
    @15
    @48
    @50
    @49
    @63
    @15
    wb
    @53
    @52
    @9
    @8
    cA
    cA
    cR
    brinxp
    syl2anc
    notbid
    rabbidva
    syl5eq
    @42
    @27
    @1
    @65
    @23
    wcel
    #
    @66
    @24
    wcel
    @55
    @56
    @2
    @0
    @57
    @67
    @41
    @58
    @59
    vy
    @9
    cR
    cps
    @29
    @32
    ordtopn2
    syl2an
    @65
    cA
    @23
    ctop
    cV
    elrestr
    syl3anc
    eqeltrrd
    @61
    eqid
    fmptd
    @30
    @24
    @61
    frn
    syl
    eqsstrd
    unssd
    unssd
    @21
    @24
    tgfiss
    syl2anc
    eqsstrd
end
