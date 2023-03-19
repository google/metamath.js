include "c0.mm"
include "cint.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wral.mm"
include "ral0.mm"
include "vex.mm"
include "elint2.mm"
include "mpbir.mm"
include "2th.mm"
include "eqriv.mm"

theorem int0
  let vx: setvar x
  let vy: setvar y


  assert |- |^| (/) = _V

  proof
    vy
    c0
    cint
    #
    cvv
    vy
    cv
    #
    @0
    wcel
    #
    @1
    cvv
    wcel
    @2
    vy
    vx
    wel
    #
    vx
    c0
    wral
    @3
    vx
    ral0
    vx
    @1
    c0
    vy
    vex
    #
    elint2
    mpbir
    @4
    2th
    eqriv
end
