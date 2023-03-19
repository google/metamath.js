include "con0.mm"
include "wtr.mm"
include "cv.mm"
include "wss.mm"
include "dftr3.mm"
include "wcel.mm"
include "word.mm"
include "vex.mm"
include "elon.mm"
include "ordelord.mm"
include "sylanb.mm"
include "ex.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "mprgbir.mm"

theorem tron
  let vx: setvar x
  let vy: setvar y


  assert |- Tr On

  proof
    con0
    wtr
    vx
    cv
    #
    con0
    wss
    vx
    con0
    vx
    con0
    dftr3
    @0
    con0
    wcel
    #
    vy
    @0
    con0
    @1
    vy
    cv
    #
    @0
    wcel
    #
    @2
    word
    #
    @2
    con0
    wcel
    @1
    @3
    @4
    @1
    @0
    word
    @3
    @4
    @0
    vx
    vex
    elon
    @0
    @2
    ordelord
    sylanb
    ex
    @2
    vy
    vex
    elon
    syl6ibr
    ssrdv
    mprgbir
end
