include "cpw.mm"
include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "cptfin.mm"
include "wceq.mm"
include "wa.mm"
include "lfinpfin.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "locfinbas.mm"
include "jca.mm"
include "ctop.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wrex.mm"
include "wral.mm"
include "cvv.mm"
include "simpr.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "distop.mm"
include "syl.mm"
include "csn.mm"
include "snelpwi.mm"
include "adantl.mm"
include "snidg.mm"
include "simpll.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "ptfinfin.mm"
include "syl2anc.mm"
include "eleq2.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "disjsn.mm"
include "necon2abii.mm"
include "syl6bbr.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "islocfin.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem locfindis
  let cC: class C
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume locfindis.1: |- Y = U. C


  assert |- ( C e. ( LocFin ` ~P X ) <-> ( C e. PtFin /\ X = Y ) )

  proof
    cC
    cX
    cpw
    #
    clocfin
    cfv
    wcel
    #
    cC
    cptfin
    wcel
    #
    cX
    cY
    wceq
    #
    wa
    #
    @1
    @2
    @3
    cC
    @0
    lfinpfin
    cC
    @0
    cX
    cY
    @0
    cuni
    cX
    cX
    unipw
    eqcomi
    #
    locfindis.1
    locfinbas
    jca
    @4
    @0
    ctop
    wcel
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    vs
    cv
    #
    @8
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
    wa
    #
    vy
    @0
    wrex
    #
    vx
    cX
    wral
    @1
    @4
    cX
    cvv
    wcel
    @6
    @4
    cX
    cY
    cvv
    @2
    @3
    simpr
    #
    @2
    cY
    cvv
    wcel
    @3
    @2
    cY
    cC
    cuni
    cvv
    locfindis.1
    cC
    cptfin
    uniexg
    syl5eqel
    adantr
    eqeltrd
    cX
    cvv
    distop
    syl
    @17
    @4
    @16
    vx
    cX
    @4
    @7
    cX
    wcel
    #
    wa
    #
    @7
    csn
    #
    @0
    wcel
    #
    @7
    @20
    wcel
    #
    @7
    @10
    wcel
    #
    vs
    cC
    crab
    #
    cfn
    wcel
    #
    @16
    @18
    @21
    @4
    @7
    cX
    snelpwi
    adantl
    @18
    @22
    @4
    @7
    cX
    snidg
    adantl
    @19
    @2
    @7
    cY
    wcel
    #
    @25
    @2
    @3
    @18
    simpll
    @4
    @18
    @26
    @4
    cX
    cY
    @7
    @17
    eleq2d
    biimpa
    vs
    cC
    @7
    cY
    locfindis.1
    ptfinfin
    syl2anc
    @15
    @22
    @25
    wa
    vy
    @20
    @0
    @8
    @20
    wceq
    #
    @9
    @22
    @14
    @25
    @8
    @20
    @7
    eleq2
    @27
    @13
    @24
    cfn
    @27
    @12
    @23
    vs
    cC
    @27
    @12
    @10
    @20
    cin
    #
    c0
    wne
    @23
    @27
    @11
    @28
    c0
    @8
    @20
    @10
    ineq2
    neeq1d
    @23
    @28
    c0
    @10
    @7
    disjsn
    necon2abii
    syl6bbr
    rabbidv
    eleq1d
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    vx
    cC
    vy
    @0
    cX
    cY
    vs
    @5
    locfindis.1
    islocfin
    syl3anbrc
    impbii
end
