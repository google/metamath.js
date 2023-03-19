include "cvv.mm"
include "wtru.mm"
include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "dfcleq.mm"
include "vex.mm"
include "tru.mm"
include "bj-vexwv.mm"
include "2th.mm"
include "mpgbir.mm"

theorem bj-df-v
  let vx: setvar x
  let vy: setvar y


  assert |- _V = { x | T. }

  proof
    cvv
    wtru
    vx
    cab
    #
    wceq
    vy
    cv
    #
    cvv
    wcel
    #
    @1
    @0
    wcel
    #
    wb
    vy
    vy
    cvv
    @0
    dfcleq
    @2
    @3
    vy
    vex
    wtru
    vx
    vy
    tru
    bj-vexwv
    2th
    mpgbir
end
