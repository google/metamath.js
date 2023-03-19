include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "nfv.mm"
include "sbco2.mm"
include "eleq1w.mm"
include "sbie.mm"
include "sbbii.mm"
include "3bitr3i.mm"

theorem bj-clelsb3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A y
  disjoint y z
  disjoint A z
  disjoint x z
  assert |- ( [ x / y ] y e. A <-> x e. A )

  proof
    vz
    cv
    cA
    wcel
    #
    vz
    vy
    wsb
    #
    vy
    vx
    wsb
    @0
    vz
    vx
    wsb
    vy
    cv
    cA
    wcel
    #
    vy
    vx
    wsb
    vx
    cv
    cA
    wcel
    #
    @0
    vz
    vx
    vy
    @0
    vy
    nfv
    sbco2
    @1
    @2
    vy
    vx
    @0
    @2
    vz
    vy
    @2
    vz
    nfv
    vz
    vy
    cA
    eleq1w
    sbie
    sbbii
    @0
    @3
    vz
    vx
    @3
    vz
    nfv
    vz
    vx
    cA
    eleq1w
    sbie
    3bitr3i
end
