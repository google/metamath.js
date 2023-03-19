include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "nfcri.mm"
include "sbco2.mm"
include "nfv.mm"
include "eleq1.mm"
include "sbie.mm"
include "sbbii.mm"
include "3bitr3i.mm"

theorem clelsb3f
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  assume clelsb3f.1: |- F/_ y A


  assert |- ( [ x / y ] y e. A <-> x e. A )

  proof
    vw
    cv
    #
    cA
    wcel
    #
    vw
    vy
    wsb
    #
    vy
    vx
    wsb
    @1
    vw
    vx
    wsb
    vy
    cv
    #
    cA
    wcel
    #
    vy
    vx
    wsb
    vx
    cv
    #
    cA
    wcel
    #
    @1
    vw
    vx
    vy
    vy
    vw
    cA
    clelsb3f.1
    nfcri
    sbco2
    @2
    @4
    vy
    vx
    @1
    @4
    vw
    vy
    @4
    vw
    nfv
    @0
    @3
    cA
    eleq1
    sbie
    sbbii
    @1
    @6
    vw
    vx
    @6
    vw
    nfv
    @0
    @5
    cA
    eleq1
    sbie
    3bitr3i
end
