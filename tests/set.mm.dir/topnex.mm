include "ctop.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cpw.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "pwnex.mm"
include "neli.mm"
include "wss.mm"
include "vex.mm"
include "distop.mm"
include "ax-mp.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "abssi.mm"
include "ssexg.mm"
include "mpan.mm"
include "mto.mm"
include "nelir.mm"

theorem topnex
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V


  assert |- Top e/ _V

  proof
    ctop
    cvv
    ctop
    cvv
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    cpw
    #
    wceq
    #
    vx
    wex
    #
    vy
    cab
    #
    cvv
    wcel
    #
    @6
    cvv
    vy
    vx
    pwnex
    neli
    @6
    ctop
    wss
    @0
    @7
    @5
    vy
    ctop
    @4
    @1
    ctop
    wcel
    #
    vx
    @4
    @8
    @3
    ctop
    wcel
    #
    @2
    cvv
    wcel
    @9
    vx
    vex
    @2
    cvv
    distop
    ax-mp
    @1
    @3
    ctop
    eleq1
    mpbiri
    exlimiv
    abssi
    @6
    ctop
    cvv
    ssexg
    mpan
    mto
    nelir
end
