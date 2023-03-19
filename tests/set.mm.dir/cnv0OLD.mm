include "c0.mm"
include "ccnv.mm"
include "relcnv.mm"
include "rel0.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "vex.mm"
include "opelcnv.mm"
include "noel.mm"
include "2false.mm"
include "bitr4i.mm"
include "eqrelriiv.mm"

theorem cnv0OLD
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' (/) = (/)

  proof
    vx
    vy
    c0
    ccnv
    #
    c0
    c0
    relcnv
    rel0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    @2
    @1
    cop
    #
    c0
    wcel
    #
    @3
    c0
    wcel
    #
    @1
    @2
    c0
    vx
    vex
    vy
    vex
    opelcnv
    @6
    @5
    @3
    noel
    @4
    noel
    2false
    bitr4i
    eqrelriiv
end
