include "cv.mm"
include "csn.mm"
include "wcel.mm"
include "wex.mm"
include "vex.mm"
include "snid.mm"
include "snex.mm"
include "eleq2.mm"
include "spcev.mm"
include "ax-mp.mm"

theorem elALT
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- E. y x e. y

  proof
    vx
    cv
    #
    @0
    csn
    #
    wcel
    #
    @0
    vy
    cv
    #
    wcel
    #
    vy
    wex
    @0
    vx
    vex
    snid
    @4
    @2
    vy
    @1
    @0
    snex
    @3
    @1
    @0
    eleq2
    spcev
    ax-mp
end
