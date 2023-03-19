include "clocfin.mm"
include "cfv.mm"
include "wcel.mm"
include "cptfin.mm"
include "cv.mm"
include "crab.mm"
include "cfn.mm"
include "cuni.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "eqid.mm"
include "locfinbas.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "locfinnei.mm"
include "syldan.mm"
include "wss.mm"
include "wi.mm"
include "inelcm.mm"
include "expcom.mm"
include "ad2antlr.mm"
include "ss2rabdv.mm"
include "ssfi.mm"
include "syl.mm"
include "expimpd.mm"
include "rexlimdvw.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "isptfin.mm"
include "mpbird.mm"

theorem lfinpfin
  let cA: class A
  let cJ: class J
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let cB: class B


  assert |- ( A e. ( LocFin ` J ) -> A e. PtFin )

  proof
    cA
    cJ
    clocfin
    cfv
    #
    wcel
    #
    cA
    cptfin
    wcel
    vx
    cv
    #
    vs
    cv
    #
    wcel
    #
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    vx
    cA
    cuni
    #
    wral
    @1
    @6
    vx
    @7
    @1
    @2
    @7
    wcel
    #
    wa
    #
    @2
    vn
    cv
    #
    wcel
    #
    @3
    @10
    cin
    c0
    wne
    #
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    @6
    @1
    @8
    @2
    cJ
    cuni
    #
    wcel
    #
    @16
    @1
    @18
    @8
    @1
    @17
    @7
    @2
    cA
    cJ
    @17
    @7
    @17
    eqid
    #
    @7
    eqid
    #
    locfinbas
    eleq2d
    biimpar
    cA
    @2
    vn
    cJ
    @17
    vs
    @19
    locfinnei
    syldan
    @9
    @15
    @6
    vn
    cJ
    @9
    @11
    @14
    @6
    @9
    @11
    wa
    #
    @5
    @13
    wss
    #
    @14
    @6
    wi
    @21
    @4
    @12
    vs
    cA
    @11
    @4
    @12
    wi
    @9
    @3
    cA
    wcel
    @4
    @11
    @12
    @2
    @3
    @10
    inelcm
    expcom
    ad2antlr
    ss2rabdv
    @14
    @22
    @6
    @13
    @5
    ssfi
    expcom
    syl
    expimpd
    rexlimdvw
    mpd
    ralrimiva
    vx
    vs
    cA
    @0
    @7
    @20
    isptfin
    mpbird
end
