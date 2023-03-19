include "cwun.mm"
include "cuni.mm"
include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "eqv.mm"
include "csn.mm"
include "wss.mm"
include "wrex.mm"
include "snex.mm"
include "wunex.mm"
include "ax-mp.mm"
include "eluni2.mm"
include "vex.mm"
include "snss.mm"
include "rexbii.mm"
include "bitri.mm"
include "mpbir.mm"
include "mpgbir.mm"

theorem uniwun
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A


  assert |- U. WUni = _V

  proof
    cwun
    cuni
    #
    cvv
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    vx
    vx
    @0
    eqv
    @2
    @1
    csn
    #
    vu
    cv
    #
    wss
    #
    vu
    cwun
    wrex
    #
    @3
    cvv
    wcel
    @6
    @1
    snex
    vu
    @3
    cvv
    wunex
    ax-mp
    @2
    @1
    @4
    wcel
    #
    vu
    cwun
    wrex
    @6
    vu
    @1
    cwun
    eluni2
    @7
    @5
    vu
    cwun
    @1
    @4
    vx
    vex
    snss
    rexbii
    bitri
    mpbir
    mpgbir
end
