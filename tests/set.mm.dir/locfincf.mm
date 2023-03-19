include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "clocfin.mm"
include "cv.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wrex.mm"
include "wral.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "toponuni.mm"
include "eqid.mm"
include "locfinbas.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "locfinnei.mm"
include "ex.mm"
include "wi.mm"
include "ssrexv.mm"
include "sylan9r.mm"
include "sylbird.mm"
include "ralrimiv.mm"
include "islocfin.mm"
include "syl3anbrc.mm"
include "ssrdv.mm"

theorem locfincf
  let cJ: class J
  let cK: class K
  let cX: class X
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume locfincf.1: |- X = U. J


  assert |- ( ( K e. ( TopOn ` X ) /\ J C_ K ) -> ( LocFin ` J ) C_ ( LocFin ` K ) )

  proof
    cK
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    cK
    wss
    #
    wa
    #
    vx
    cJ
    clocfin
    cfv
    #
    cK
    clocfin
    cfv
    #
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    cK
    ctop
    wcel
    #
    cK
    cuni
    #
    @5
    cuni
    #
    wceq
    vy
    cv
    #
    vn
    cv
    #
    wcel
    vs
    cv
    @13
    cin
    c0
    wne
    vs
    @5
    crab
    cfn
    wcel
    wa
    #
    vn
    cK
    wrex
    #
    vy
    @10
    wral
    @7
    @0
    @9
    @1
    @6
    cX
    cK
    topontop
    ad2antrr
    @8
    cX
    @10
    @11
    @0
    cX
    @10
    wceq
    @1
    @6
    cX
    cK
    toponuni
    ad2antrr
    #
    @6
    cX
    @11
    wceq
    @2
    @5
    cJ
    cX
    @11
    locfincf.1
    @11
    eqid
    #
    locfinbas
    adantl
    eqtr3d
    @8
    @15
    vy
    @10
    @8
    @12
    @10
    wcel
    @12
    cX
    wcel
    #
    @15
    @8
    cX
    @10
    @12
    @16
    eleq2d
    @6
    @18
    @14
    vn
    cJ
    wrex
    #
    @2
    @15
    @6
    @18
    @19
    @5
    @12
    vn
    cJ
    cX
    vs
    locfincf.1
    locfinnei
    ex
    @1
    @19
    @15
    wi
    @0
    @14
    vn
    cJ
    cK
    ssrexv
    adantl
    sylan9r
    sylbird
    ralrimiv
    vy
    @5
    vn
    cK
    @10
    @11
    vs
    @10
    eqid
    @17
    islocfin
    syl3anbrc
    ex
    ssrdv
end
