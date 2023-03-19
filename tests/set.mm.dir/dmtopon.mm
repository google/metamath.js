include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "ctop.mm"
include "crab.mm"
include "ctopon.mm"
include "cpw.mm"
include "vpwex.mm"
include "pwex.mm"
include "eqcom.mm"
include "rabbii.mm"
include "cab.mm"
include "rabssab.mm"
include "pwpwssunieq.mm"
include "sstri.mm"
include "eqsstri.mm"
include "ssexi.mm"
include "df-topon.mm"
include "dmmpti.mm"

theorem dmtopon
  let vx: setvar x
  let vy: setvar y


  assert |- dom TopOn = _V

  proof
    vx
    cvv
    vx
    cv
    #
    vy
    cv
    cuni
    #
    wceq
    #
    vy
    ctop
    crab
    #
    ctopon
    @3
    @0
    cpw
    #
    cpw
    #
    @4
    vx
    vpwex
    pwex
    @3
    @1
    @0
    wceq
    #
    vy
    ctop
    crab
    #
    @5
    @2
    @6
    vy
    ctop
    @0
    @1
    eqcom
    rabbii
    @7
    @6
    vy
    cab
    @5
    @6
    vy
    ctop
    rabssab
    vy
    @0
    pwpwssunieq
    sstri
    eqsstri
    ssexi
    vy
    vx
    df-topon
    dmmpti
end
