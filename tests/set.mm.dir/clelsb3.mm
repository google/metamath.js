include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "nfv.mm"
include "sbco2.mm"
include "eleq1.mm"
include "sbie.mm"
include "sbbii.mm"
include "3bitr3i.mm"

theorem clelsb3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w

  disjoint A y
  disjoint w y
  disjoint A w
  disjoint w x
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
    @1
    vy
    nfv
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
