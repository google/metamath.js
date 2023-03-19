include "cpreset.mm"
include "wcel.mm"
include "wss.mm"
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
include "cple.mm"
include "fvex.mm"
include "inex1.mm"
include "eqeltri.mm"
include "eqid.mm"
include "ordtval.mm"
include "mp1i.mm"
include "ctop.mm"
include "ordttop.mm"
include "ax-mp.mm"
include "cbs.mm"
include "ssex.mm"
include "resttop.mm"
include "sylancr.mm"
include "adantl.mm"
include "cress.mm"
include "ressprs.mm"
include "prsdm.mm"
include "syl.mm"
include "ressbas2.mm"
include "syl6eqel.mm"
include "ressle.mm"
include "sqxpeqd.mm"
include "ineq12d.mm"
include "dmeqd.mm"
include "3eqtr4d.mm"
include "prsss.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "sseqin2.mm"
include "sylib.mm"
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
include "simpr.mm"
include "sseldi.mm"
include "adantr.mm"
include "brinxp.mm"
include "syl2anc.mm"
include "notbid.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "simpl.mm"
include "inss1.mm"
include "sseli.mm"
include "ordtopn1.mm"
include "mpan.mm"
include "syl2an.mm"
include "eqeltrrd.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "ordtopn2.mm"
include "unssd.mm"
include "tgfiss.mm"

theorem ordtrestNEW
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( ( K e. Preset /\ A C_ B ) -> ( ordTop ` ( .<_ i^i ( A X. A ) ) ) C_ ( ( ordTop ` .<_ ) |`t A ) )

  proof
    cK
    cpreset
    wcel
    #
    cA
    cB
    wss
    #
    wa
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
    c.le
    cordt
    cfv
    #
    cA
    crest
    co
    #
    @4
    cvv
    wcel
    @5
    @22
    wceq
    @2
    c.le
    @3
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
    @25
    @26
    cK
    cple
    fvex
    inex1
    eqeltri
    #
    inex1
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
    mp1i
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
    @1
    @28
    @0
    @1
    @23
    ctop
    wcel
    #
    cA
    cvv
    wcel
    #
    @28
    c.le
    cvv
    wcel
    #
    @29
    @27
    c.le
    cvv
    ordttop
    #
    ax-mp
    cA
    cB
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
    ssex
    #
    cA
    @23
    cvv
    resttop
    sylancr
    adantl
    @2
    @7
    @20
    @24
    @2
    @6
    @24
    @2
    @6
    c.le
    cdm
    #
    cA
    cin
    #
    @24
    @2
    @25
    @3
    cin
    #
    cdm
    #
    cA
    @6
    @35
    @2
    cK
    cA
    cress
    co
    #
    cple
    cfv
    #
    @38
    cbs
    cfv
    #
    @40
    cxp
    #
    cin
    #
    cdm
    #
    @40
    @37
    cA
    @2
    @38
    cpreset
    wcel
    @43
    @40
    wceq
    cA
    cB
    cK
    ordtNEW.b
    ressprs
    @40
    @38
    @42
    @40
    eqid
    @42
    eqid
    prsdm
    syl
    @2
    @36
    @42
    @2
    @25
    @39
    @3
    @41
    @1
    @25
    @39
    wceq
    #
    @0
    @1
    @30
    @44
    @1
    cA
    @40
    cvv
    cA
    cB
    @38
    cK
    @38
    eqid
    #
    ordtNEW.b
    ressbas2
    #
    @38
    cbs
    fvex
    syl6eqel
    cA
    cK
    @25
    cvv
    @38
    @45
    @25
    eqid
    ressle
    syl
    adantl
    @2
    cA
    @40
    @1
    cA
    @40
    wceq
    @0
    @46
    adantl
    #
    sqxpeqd
    ineq12d
    dmeqd
    @47
    3eqtr4d
    @2
    @4
    @36
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsss
    dmeqd
    @2
    cA
    @34
    wss
    #
    @35
    cA
    wceq
    @0
    @48
    @1
    @0
    @34
    cB
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsdm
    sseq2d
    biimpar
    cA
    @34
    sseqin2
    sylib
    3eqtr4d
    #
    @2
    @29
    @30
    @34
    @23
    wcel
    #
    @35
    @24
    wcel
    @31
    @29
    @2
    @27
    @32
    mp1i
    @1
    @30
    @0
    @33
    adantl
    #
    @2
    @23
    @34
    ctopon
    cfv
    wcel
    #
    @50
    @31
    @52
    @2
    @27
    c.le
    cvv
    @34
    @34
    eqid
    #
    ordttopon
    mp1i
    @34
    @23
    toponmax
    syl
    @34
    cA
    @23
    ctop
    cvv
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
    @35
    @11
    vy
    @35
    crab
    #
    cmpt
    #
    crn
    #
    @24
    @2
    @13
    @55
    @2
    vx
    @6
    @12
    @35
    @54
    @49
    @2
    @6
    @35
    wceq
    #
    @12
    @54
    wceq
    @49
    @11
    vy
    @6
    @35
    rabeq
    syl
    mpteq12dv
    rneqd
    @2
    @35
    @24
    @55
    wf
    @56
    @24
    wss
    @2
    vx
    @35
    @54
    @24
    @55
    @2
    @9
    @35
    wcel
    #
    wa
    #
    @8
    @9
    c.le
    wbr
    #
    wn
    #
    vy
    @34
    crab
    #
    cA
    cin
    #
    @54
    @24
    @59
    @63
    @61
    vy
    @35
    crab
    @54
    @61
    vy
    @34
    cA
    inrab2
    @59
    @61
    @11
    vy
    @35
    @59
    @8
    @35
    wcel
    #
    wa
    #
    @60
    @10
    @65
    @8
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    @60
    @10
    wb
    @65
    @35
    cA
    @8
    @34
    cA
    inss2
    #
    @59
    @64
    simpr
    sseldi
    #
    @59
    @67
    @64
    @59
    @35
    cA
    @9
    @68
    @2
    @58
    simpr
    sseldi
    adantr
    #
    @8
    @9
    cA
    cA
    c.le
    brinxp
    syl2anc
    notbid
    rabbidva
    syl5eq
    @59
    @29
    @30
    @62
    @23
    wcel
    #
    @63
    @24
    wcel
    @31
    @29
    @59
    @27
    @32
    mp1i
    #
    @2
    @30
    @58
    @51
    adantr
    #
    @2
    @0
    @9
    @34
    wcel
    #
    @71
    @58
    @0
    @1
    simpl
    #
    @35
    @34
    @9
    @34
    cA
    inss1
    sseli
    #
    @74
    @71
    @0
    @31
    @74
    @71
    @27
    vy
    @9
    c.le
    cvv
    @34
    @53
    ordtopn1
    mpan
    adantl
    syl2an
    @62
    cA
    @23
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    @55
    eqid
    fmptd
    @35
    @24
    @55
    frn
    syl
    eqsstrd
    @2
    @19
    vx
    @35
    @16
    vy
    @35
    crab
    #
    cmpt
    #
    crn
    #
    @24
    @2
    @18
    @78
    @2
    vx
    @6
    @17
    @35
    @77
    @49
    @2
    @57
    @17
    @77
    wceq
    @49
    @16
    vy
    @6
    @35
    rabeq
    syl
    mpteq12dv
    rneqd
    @2
    @35
    @24
    @78
    wf
    @79
    @24
    wss
    @2
    vx
    @35
    @77
    @24
    @78
    @59
    @9
    @8
    c.le
    wbr
    #
    wn
    #
    vy
    @34
    crab
    #
    cA
    cin
    #
    @77
    @24
    @59
    @83
    @81
    vy
    @35
    crab
    @77
    @81
    vy
    @34
    cA
    inrab2
    @59
    @81
    @16
    vy
    @35
    @65
    @80
    @15
    @65
    @67
    @66
    @80
    @15
    wb
    @70
    @69
    @9
    @8
    cA
    cA
    c.le
    brinxp
    syl2anc
    notbid
    rabbidva
    syl5eq
    @59
    @29
    @30
    @82
    @23
    wcel
    #
    @83
    @24
    wcel
    @72
    @73
    @2
    @0
    @74
    @84
    @58
    @75
    @76
    @74
    @84
    @0
    @31
    @74
    @84
    @27
    vy
    @9
    c.le
    cvv
    @34
    @53
    ordtopn2
    mpan
    adantl
    syl2an
    @82
    cA
    @23
    ctop
    cvv
    elrestr
    syl3anc
    eqeltrrd
    @78
    eqid
    fmptd
    @35
    @24
    @78
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
