include "weq.mm"
include "cv.mm"
include "wsbc.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "vex.mm"
include "frege54cor1c.mm"
include "frege53c.mm"
include "ax-mp.mm"

theorem frege55lem2c
  let vx: setvar x
  let vz: setvar z
  let cA: class A

  disjoint x z
  assert |- ( x = A -> [. A / z ]. z = x )

  proof
    vz
    vx
    weq
    #
    vz
    vx
    cv
    #
    wsbc
    @1
    cA
    wceq
    @0
    vz
    cA
    wsbc
    wi
    vz
    @1
    cvv
    vx
    vex
    frege54cor1c
    @0
    vz
    @1
    cA
    frege53c
    ax-mp
end
