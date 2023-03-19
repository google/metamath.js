include "cvv.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "ssv.mm"
include "selpw.mm"
include "mpbir.mm"
include "vex.mm"
include "2th.mm"
include "eqriv.mm"

theorem pwv
  let vx: setvar x


  assert |- ~P _V = _V

  proof
    vx
    cvv
    cpw
    #
    cvv
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cvv
    wcel
    @2
    @1
    cvv
    wss
    @1
    ssv
    vx
    cvv
    selpw
    mpbir
    vx
    vex
    2th
    eqriv
end
