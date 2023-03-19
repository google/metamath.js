include "cv.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "cvv.mm"
include "wceq.mm"
include "setind.mm"
include "vex.mm"
include "r1elss.mm"
include "biimpri.mm"
include "mpg.mm"

theorem unir1
  let vx: setvar x


  assert |- U. ( R1 " On ) = _V

  proof
    vx
    cv
    #
    cr1
    con0
    cima
    cuni
    #
    wss
    #
    @0
    @1
    wcel
    #
    wi
    @1
    cvv
    wceq
    vx
    vx
    @1
    setind
    @3
    @2
    @0
    vx
    vex
    r1elss
    biimpri
    mpg
end
