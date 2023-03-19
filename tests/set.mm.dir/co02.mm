include "c0.mm"
include "ccom.mm"
include "relco.mm"
include "rel0.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "br0.mm"
include "intnanr.mm"
include "nex.mm"
include "vex.mm"
include "opelco.mm"
include "mtbir.mm"
include "noel.mm"
include "2false.mm"
include "eqrelriiv.mm"

theorem co02
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A o. (/) ) = (/)

  proof
    vx
    vy
    cA
    c0
    ccom
    #
    c0
    cA
    c0
    relco
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
    #
    @3
    c0
    wcel
    @4
    @1
    vz
    cv
    #
    c0
    wbr
    #
    @5
    @2
    cA
    wbr
    #
    wa
    #
    vz
    wex
    @8
    vz
    @6
    @7
    @1
    @5
    br0
    intnanr
    nex
    vz
    @1
    @2
    cA
    c0
    vx
    vex
    vy
    vex
    opelco
    mtbir
    @3
    noel
    2false
    eqrelriiv
end
