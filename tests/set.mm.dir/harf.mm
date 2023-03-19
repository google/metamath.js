include "cvv.mm"
include "con0.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "char.mm"
include "df-har.mm"
include "hartogs.mm"
include "fmpti.mm"

theorem harf
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y


  assert |- har : _V --> On

  proof
    vx
    cvv
    con0
    vy
    cv
    vx
    cv
    #
    cdom
    wbr
    vy
    con0
    crab
    char
    vx
    vy
    df-har
    vy
    @0
    cvv
    hartogs
    fmpti
end
