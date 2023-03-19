include "ccmp.mm"
include "wcel.mm"
include "clocfin.mm"
include "cfv.mm"
include "cfn.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wss.mm"
include "cv.mm"
include "cuni.mm"
include "cin.mm"
include "wne.mm"
include "crab.mm"
include "wral.mm"
include "cpw.mm"
include "wrex.mm"
include "wel.mm"
include "locfinnei.mm"
include "ralrimiva.mm"
include "cmpcov2.mm"
include "sylan2.mm"
include "wi.mm"
include "elfpw.mm"
include "ciun.mm"
include "simplrr.mm"
include "eldifsn.mm"
include "wex.mm"
include "simplrl.mm"
include "simprr.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elunii.mm"
include "syl6eleqr.mm"
include "ancoms.mm"
include "adantl.mm"
include "locfinbas.mm"
include "ad3antrrr.mm"
include "eleqtrrd.mm"
include "simplr.mm"
include "eleqtrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "reximddv.mm"
include "expr.mm"
include "exlimdv.mm"
include "n0.mm"
include "eliun.mm"
include "3imtr4g.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "iunfi.mm"
include "ex.mm"
include "ssfi.mm"
include "expcom.mm"
include "sylan9.mm"
include "sylan2b.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "jca.mm"
include "ctop.mm"
include "cmptop.mm"
include "finlocfin.mm"
include "3expib.mm"
include "syl.mm"
include "impbid.mm"

theorem locfincmp
  let cC: class C
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume locfincmp.1: |- X = U. J
  assume locfincmp.2: |- Y = U. C


  assert |- ( J e. Comp -> ( C e. ( LocFin ` J ) <-> ( C e. Fin /\ X = Y ) ) )

  proof
    cJ
    ccmp
    wcel
    #
    cC
    cJ
    clocfin
    cfv
    wcel
    #
    cC
    cfn
    wcel
    #
    cX
    cY
    wceq
    #
    wa
    #
    @0
    @1
    @4
    @0
    @1
    wa
    #
    @2
    @3
    @5
    cC
    c0
    csn
    #
    cdif
    #
    @6
    cun
    #
    cfn
    wcel
    #
    cC
    @8
    wss
    @2
    @5
    @7
    cfn
    wcel
    #
    @6
    cfn
    wcel
    @9
    @5
    cX
    vc
    cv
    #
    cuni
    #
    wceq
    #
    vs
    cv
    #
    vo
    cv
    #
    cin
    #
    c0
    wne
    #
    vs
    cC
    crab
    #
    cfn
    wcel
    #
    vo
    @11
    wral
    #
    wa
    #
    vc
    cJ
    cpw
    cfn
    cin
    #
    wrex
    #
    @10
    @1
    @0
    vx
    vo
    wel
    @19
    wa
    vo
    cJ
    wrex
    #
    vx
    cX
    wral
    @23
    @1
    @24
    vx
    cX
    cC
    vx
    cv
    #
    vo
    cJ
    cX
    vs
    locfincmp.1
    locfinnei
    ralrimiva
    @19
    vx
    vo
    cJ
    cX
    vc
    locfincmp.1
    cmpcov2
    sylan2
    @5
    @21
    @10
    vc
    @22
    @11
    @22
    wcel
    @5
    @11
    cJ
    wss
    #
    @11
    cfn
    wcel
    #
    wa
    #
    @21
    @10
    wi
    @11
    cJ
    elfpw
    @5
    @28
    wa
    #
    @13
    @20
    @10
    @29
    @13
    wa
    #
    @27
    @7
    vo
    @11
    @18
    ciun
    #
    wss
    #
    @20
    @10
    wi
    @5
    @26
    @27
    @13
    simplrr
    @30
    vx
    @7
    @31
    @25
    @7
    wcel
    @25
    cC
    wcel
    #
    @25
    c0
    wne
    #
    wa
    @30
    @25
    @31
    wcel
    #
    @25
    cC
    c0
    eldifsn
    @30
    @33
    @34
    @35
    @30
    @33
    wa
    #
    vy
    vx
    wel
    #
    vy
    wex
    @25
    @18
    wcel
    #
    vo
    @11
    wrex
    #
    @34
    @35
    @36
    @37
    @39
    vy
    @30
    @33
    @37
    @39
    @30
    @33
    @37
    wa
    #
    wa
    #
    vy
    vo
    wel
    #
    @38
    vo
    @11
    @41
    vo
    vc
    wel
    #
    @42
    wa
    #
    wa
    #
    @33
    @25
    @15
    cin
    #
    c0
    wne
    #
    @38
    @30
    @33
    @37
    @44
    simplrl
    @45
    @37
    @42
    @47
    @30
    @33
    @37
    @44
    simplrr
    @41
    @43
    @42
    simprr
    vy
    cv
    #
    @25
    @15
    inelcm
    syl2anc
    @17
    @47
    vs
    @25
    cC
    @14
    @25
    wceq
    @16
    @46
    c0
    @14
    @25
    @15
    ineq1
    neeq1d
    elrab
    sylanbrc
    @41
    @48
    @12
    wcel
    @42
    vo
    @11
    wrex
    @41
    @48
    cX
    @12
    @41
    @48
    cY
    cX
    @40
    @48
    cY
    wcel
    #
    @30
    @37
    @33
    @49
    @37
    @33
    wa
    @48
    cC
    cuni
    cY
    @48
    @25
    cC
    elunii
    locfincmp.2
    syl6eleqr
    ancoms
    adantl
    @5
    @3
    @28
    @13
    @40
    @1
    @3
    @0
    cC
    cJ
    cX
    cY
    locfincmp.1
    locfincmp.2
    locfinbas
    adantl
    #
    ad3antrrr
    eleqtrrd
    @29
    @13
    @40
    simplr
    eleqtrd
    vo
    @48
    @11
    eluni2
    sylib
    reximddv
    expr
    exlimdv
    vy
    @25
    n0
    vo
    @25
    @11
    @18
    eliun
    3imtr4g
    expimpd
    syl5bi
    ssrdv
    @27
    @20
    @31
    cfn
    wcel
    #
    @32
    @10
    @27
    @20
    @51
    vo
    @11
    @18
    iunfi
    ex
    @51
    @32
    @10
    @31
    @7
    ssfi
    expcom
    sylan9
    syl2anc
    expimpd
    sylan2b
    rexlimdva
    mpd
    c0
    snfi
    @7
    @6
    unfi
    sylancl
    cC
    cC
    @6
    cun
    @8
    cC
    @6
    ssun1
    cC
    @6
    undif1
    sseqtr4i
    @8
    cC
    ssfi
    sylancl
    @50
    jca
    ex
    @0
    cJ
    ctop
    wcel
    #
    @4
    @1
    wi
    cJ
    cmptop
    @52
    @2
    @3
    @1
    cC
    cJ
    cX
    cY
    locfincmp.1
    locfincmp.2
    finlocfin
    3expib
    syl
    impbid
end
