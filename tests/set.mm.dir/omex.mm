include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "csuc.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "com.mm"
include "wss.mm"
include "cvv.mm"
include "zfinf2.mm"
include "wi.mm"
include "ax-1.mm"
include "ralimi2.mm"
include "peano5.mm"
include "sylan2.mm"
include "eximi.mm"
include "vex.mm"
include "ssex.mm"
include "exlimiv.mm"
include "mp2b.mm"

theorem omex
  let vx: setvar x
  let vy: setvar y


  assert |- _om e. _V

  proof
    c0
    vx
    cv
    #
    wcel
    #
    vy
    cv
    #
    csuc
    @0
    wcel
    #
    vy
    @0
    wral
    #
    wa
    #
    vx
    wex
    com
    @0
    wss
    #
    vx
    wex
    com
    cvv
    wcel
    #
    vx
    vy
    zfinf2
    @5
    @6
    vx
    @4
    @1
    @2
    @0
    wcel
    @3
    wi
    #
    vy
    com
    wral
    @6
    @3
    @8
    vy
    @0
    com
    @8
    @2
    com
    wcel
    ax-1
    ralimi2
    vy
    @0
    peano5
    sylan2
    eximi
    @6
    @7
    vx
    com
    @0
    vx
    vex
    ssex
    exlimiv
    mp2b
end
