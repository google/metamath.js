include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wral.mm"
include "wse.mm"
include "rabexg.mm"
include "ralrimivw.mm"
include "df-se.mm"
include "sylibr.mm"

theorem exse
  let cA: class A
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. V -> R Se A )

  proof
    cA
    cV
    wcel
    #
    vy
    cv
    vx
    cv
    cR
    wbr
    #
    vy
    cA
    crab
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
    @2
    vx
    cA
    @1
    vy
    cA
    cV
    rabexg
    ralrimivw
    vx
    vy
    cA
    cR
    df-se
    sylibr
end
