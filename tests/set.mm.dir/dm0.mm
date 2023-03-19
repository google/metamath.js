include "c0.mm"
include "cdm.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "noel.mm"
include "nex.mm"
include "vex.mm"
include "eldm2.mm"
include "mtbir.mm"
include "nel0.mm"

theorem dm0
  let vx: setvar x
  let vy: setvar y


  assert |- dom (/) = (/)

  proof
    vx
    c0
    cdm
    #
    vx
    cv
    #
    @0
    wcel
    @1
    vy
    cv
    cop
    #
    c0
    wcel
    #
    vy
    wex
    @3
    vy
    @2
    noel
    nex
    vy
    @1
    c0
    vx
    vex
    eldm2
    mtbir
    nel0
end
