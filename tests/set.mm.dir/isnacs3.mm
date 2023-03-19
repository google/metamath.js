include "cnacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cv.mm"
include "cipo.mm"
include "cdrs.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "nacsacs.mm"
include "acsmred.mm"
include "cmrc.mm"
include "wceq.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "simpll.mm"
include "cacs.mm"
include "wss.mm"
include "ad2antrr.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "acsdrsel.mm"
include "syl3anc.mm"
include "eqid.mm"
include "nacsfg.mm"
include "syl2anc.mm"
include "wb.mm"
include "mrefg2.mm"
include "syl.mm"
include "mpbid.mm"
include "elfpw.mm"
include "fissuni.mm"
include "sylbi.mm"
include "ipodrsfi.mm"
include "3expb.mm"
include "sylan2b.mm"
include "sstr.mm"
include "ancoms.mm"
include "simprr.mm"
include "simprl.mm"
include "sseldd.mm"
include "mrcsscl.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "simplrl.mm"
include "elssuni.mm"
include "eqssd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "expr.mm"
include "syl5.mm"
include "expd.mm"
include "rexlimdva.mm"
include "expdimp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "simpl.mm"
include "adantl.mm"
include "sseld.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "imp.mm"
include "isacs3.mm"
include "sylanbrc.mm"
include "cima.mm"
include "mrcid.mm"
include "adantlr.mm"
include "mress.mm"
include "acsficld.mm"
include "eqtr3d.mm"
include "cvv.mm"
include "wfn.mm"
include "wf.mm"
include "mrcf.mm"
include "ffn.mm"
include "mrcss.mm"
include "vex.mm"
include "fpwipodrs.mm"
include "mp1i.mm"
include "inss1.mm"
include "sspwb.mm"
include "sylib.mm"
include "syl5ss.mm"
include "fvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "a1i.mm"
include "ipodrsima.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "elpw.mm"
include "sylibr.mm"
include "simplr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "unieq.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "fvelimab.mm"
include "eqcom.mm"
include "rexbii.mm"
include "mpbird.mm"
include "isnacs.mm"
include "impbii.mm"

theorem isnacs3
  let cC: class C
  let cX: class X
  let vs: setvar s
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vt: setvar t

  disjoint C s
  disjoint X s
  disjoint C g
  disjoint C h
  disjoint C i
  disjoint g h
  disjoint g i
  disjoint g s
  disjoint h i
  disjoint h s
  disjoint i s
  disjoint C t
  disjoint X g
  disjoint X h
  disjoint X i
  disjoint X t
  disjoint g t
  disjoint h t
  disjoint s t
  assert |- ( C e. ( NoeACS ` X ) <-> ( C e. ( Moore ` X ) /\ A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. s ) ) )

  proof
    cC
    cX
    cnacs
    cfv
    wcel
    #
    cC
    cX
    cmre
    cfv
    wcel
    #
    vs
    cv
    #
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @2
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vs
    cC
    cpw
    #
    wral
    #
    wa
    #
    @0
    @1
    @9
    @0
    cC
    cX
    cC
    cX
    nacsacs
    #
    acsmred
    #
    @0
    @7
    vs
    @8
    @0
    @2
    @8
    wcel
    #
    wa
    #
    @4
    @6
    @14
    @4
    wa
    #
    @5
    vg
    cv
    #
    cC
    cmrc
    cfv
    #
    cfv
    #
    wceq
    #
    vg
    @5
    cpw
    cfn
    cin
    #
    wrex
    #
    @6
    @15
    @19
    vg
    cX
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @21
    @15
    @0
    @5
    cC
    wcel
    #
    @24
    @0
    @13
    @4
    simpll
    @15
    cC
    cX
    cacs
    cfv
    wcel
    #
    @2
    cC
    wss
    #
    @4
    @25
    @0
    @26
    @13
    @4
    @11
    ad2antrr
    @13
    @27
    @0
    @4
    @2
    cC
    elpwi
    #
    ad2antlr
    @14
    @4
    simpr
    cC
    cX
    @2
    acsdrsel
    syl3anc
    cC
    @5
    vg
    @17
    cX
    @17
    eqid
    #
    nacsfg
    syl2anc
    @0
    @24
    @21
    wb
    #
    @13
    @4
    @0
    @1
    @30
    @12
    cC
    @5
    vg
    @17
    cX
    @29
    mrefg2
    syl
    ad2antrr
    mpbid
    @15
    @19
    @6
    vg
    @20
    @16
    @20
    wcel
    #
    @16
    vh
    cv
    #
    cuni
    #
    wss
    #
    vh
    @2
    cpw
    cfn
    cin
    #
    wrex
    #
    @15
    @19
    @6
    wi
    #
    @31
    @16
    @5
    wss
    @16
    cfn
    wcel
    wa
    @36
    @16
    @5
    elfpw
    @16
    @2
    vh
    fissuni
    sylbi
    @15
    @34
    @37
    vh
    @35
    @14
    @4
    @32
    @35
    wcel
    #
    @34
    @37
    wi
    #
    @4
    @38
    wa
    @33
    vi
    cv
    #
    wss
    #
    vi
    @2
    wrex
    #
    @14
    @39
    @38
    @4
    @32
    @2
    wss
    #
    @32
    cfn
    wcel
    #
    wa
    @42
    @32
    @2
    elfpw
    @4
    @43
    @44
    @42
    vi
    @2
    @32
    ipodrsfi
    3expb
    sylan2b
    @14
    @41
    @39
    vi
    @2
    @14
    @40
    @2
    wcel
    #
    wa
    #
    @41
    @34
    @37
    @41
    @34
    wa
    @16
    @40
    wss
    #
    @46
    @37
    @34
    @41
    @47
    @16
    @33
    @40
    sstr
    ancoms
    @14
    @45
    @47
    @37
    @14
    @45
    @47
    wa
    #
    wa
    #
    @19
    @6
    @49
    @19
    wa
    #
    @5
    @40
    @2
    @50
    @5
    @40
    @50
    @5
    @18
    @40
    @49
    @19
    simpr
    @49
    @18
    @40
    wss
    #
    @19
    @49
    @1
    @47
    @40
    cC
    wcel
    @51
    @0
    @1
    @13
    @48
    @12
    ad2antrr
    @14
    @45
    @47
    simprr
    @49
    @2
    cC
    @40
    @13
    @27
    @0
    @48
    @28
    ad2antlr
    @14
    @45
    @47
    simprl
    sseldd
    cC
    @16
    @17
    @40
    cX
    @29
    mrcsscl
    syl3anc
    adantr
    eqsstrd
    @50
    @45
    @40
    @5
    wss
    @14
    @45
    @47
    @19
    simplrl
    #
    @40
    @2
    elssuni
    syl
    eqssd
    @52
    eqeltrd
    ex
    expr
    syl5
    expd
    rexlimdva
    syl5
    expdimp
    rexlimdv
    syl5
    rexlimdv
    mpd
    ex
    ralrimiva
    jca
    @10
    @26
    vt
    cv
    #
    @18
    wceq
    #
    vg
    @23
    wrex
    #
    vt
    cC
    wral
    @0
    @10
    @1
    @4
    @25
    wi
    #
    vs
    @8
    wral
    #
    @26
    @1
    @9
    simpl
    @1
    @9
    @57
    @1
    @7
    @56
    vs
    @8
    @1
    @13
    wa
    #
    @6
    @25
    @4
    @58
    @2
    cC
    @5
    @13
    @27
    @1
    @28
    adantl
    sseld
    imim2d
    ralimdva
    imp
    cC
    cX
    vs
    isacs3
    sylanbrc
    #
    @10
    @55
    vt
    cC
    @10
    @53
    cC
    wcel
    #
    wa
    #
    @55
    @54
    vg
    @53
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @61
    @18
    @53
    wceq
    #
    vg
    @63
    wrex
    #
    @64
    @61
    @53
    @17
    @63
    cima
    #
    wcel
    #
    @66
    @61
    @53
    @67
    cuni
    #
    @67
    @61
    @53
    @17
    cfv
    #
    @53
    @69
    @1
    @60
    @70
    @53
    wceq
    @9
    cC
    @53
    @17
    cX
    @29
    mrcid
    adantlr
    @61
    cC
    @53
    @17
    cX
    @10
    @26
    @60
    @59
    adantr
    @29
    @1
    @60
    @53
    cX
    wss
    #
    @9
    cC
    @53
    cX
    mress
    #
    adantlr
    acsficld
    eqtr3d
    @61
    @67
    cipo
    cfv
    #
    cdrs
    wcel
    #
    @69
    @67
    wcel
    #
    @1
    @60
    @74
    @9
    @1
    @60
    wa
    #
    vh
    vg
    cX
    @63
    @17
    cvv
    @1
    @17
    @22
    wfn
    #
    @60
    @1
    @22
    cC
    @17
    wf
    #
    @77
    cC
    @17
    cX
    @29
    mrcf
    #
    @22
    cC
    @17
    ffn
    syl
    adantr
    #
    @1
    @16
    @32
    wss
    #
    @32
    cX
    wss
    #
    wa
    @18
    @32
    @17
    cfv
    wss
    #
    @60
    @1
    @81
    @82
    @83
    cC
    @16
    @17
    @32
    cX
    @29
    mrcss
    3expb
    adantlr
    @53
    cvv
    wcel
    @63
    cipo
    cfv
    cdrs
    wcel
    @76
    vt
    vex
    @53
    cvv
    fpwipodrs
    mp1i
    @76
    @63
    @62
    @22
    @62
    cfn
    inss1
    @76
    @71
    @62
    @22
    wss
    @72
    @53
    cX
    sspwb
    sylib
    syl5ss
    #
    @67
    cvv
    wcel
    #
    @76
    @17
    cvv
    wcel
    @85
    cC
    cmrc
    fvex
    @17
    @63
    cvv
    imaexg
    ax-mp
    #
    a1i
    ipodrsima
    adantlr
    @61
    @67
    @8
    wcel
    #
    @9
    @74
    @75
    wi
    #
    @1
    @60
    @87
    @9
    @76
    @67
    cC
    wss
    #
    @87
    @1
    @89
    @60
    @1
    @67
    @17
    crn
    #
    cC
    @17
    @63
    imassrn
    @1
    @78
    @90
    cC
    wss
    @79
    @22
    cC
    @17
    frn
    syl
    syl5ss
    adantr
    @67
    cC
    @86
    elpw
    sylibr
    adantlr
    @1
    @9
    @60
    simplr
    @7
    @88
    vs
    @67
    @8
    @2
    @67
    wceq
    #
    @4
    @74
    @6
    @75
    @91
    @3
    @73
    cdrs
    @2
    @67
    cipo
    fveq2
    eleq1d
    @91
    @5
    @69
    @2
    @67
    @2
    @67
    unieq
    @91
    id
    eleq12d
    imbi12d
    rspcva
    syl2anc
    mpd
    eqeltrd
    @1
    @60
    @68
    @66
    wb
    #
    @9
    @76
    @77
    @63
    @22
    wss
    @92
    @80
    @84
    vg
    @22
    @63
    @53
    @17
    fvelimab
    syl2anc
    adantlr
    mpbid
    @54
    @65
    vg
    @63
    @53
    @18
    eqcom
    rexbii
    sylibr
    @1
    @55
    @64
    wb
    @9
    @60
    cC
    @53
    vg
    @17
    cX
    @29
    mrefg2
    ad2antrr
    mpbird
    ralrimiva
    cC
    vg
    @17
    cX
    vt
    @29
    isnacs
    sylanbrc
    impbii
end
