include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wral.mm"
include "wse.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "vex.mm"
include "breldm.mm"
include "adantl.mm"
include "abssi.mm"
include "eqsstri.mm"
include "dmexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "ralrimivw.mm"
include "df-se.mm"
include "sylibr.mm"

theorem exse2
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. V -> R Se A )

  proof
    cR
    cV
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    vy
    cA
    crab
    #
    cvv
    wcel
    #
    vx
    cA
    wral
    cA
    cR
    wse
    @0
    @5
    vx
    cA
    @0
    @4
    cR
    cdm
    #
    wss
    @6
    cvv
    wcel
    @5
    @4
    @1
    cA
    wcel
    #
    @3
    wa
    #
    vy
    cab
    @6
    @3
    vy
    cA
    df-rab
    @8
    vy
    @6
    @3
    @1
    @6
    wcel
    @7
    @1
    @2
    cR
    vy
    vex
    vx
    vex
    breldm
    adantl
    abssi
    eqsstri
    cR
    cV
    dmexg
    @4
    @6
    cvv
    ssexg
    sylancr
    ralrimivw
    vx
    vy
    cA
    cR
    df-se
    sylibr
end
