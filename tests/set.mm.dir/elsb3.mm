include "wel.mm"
include "wsb.mm"
include "nfv.mm"
include "sbco2.mm"
include "elequ1.mm"
include "sbie.mm"
include "sbbii.mm"
include "3bitr3i.mm"

theorem elsb3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w y
  disjoint w z
  disjoint w x
  assert |- ( [ x / y ] y e. z <-> x e. z )

  proof
    vw
    vz
    wel
    #
    vw
    vy
    wsb
    #
    vy
    vx
    wsb
    @0
    vw
    vx
    wsb
    vy
    vz
    wel
    #
    vy
    vx
    wsb
    vx
    vz
    wel
    #
    @0
    vw
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
    vw
    vy
    @2
    vw
    nfv
    vw
    vy
    vz
    elequ1
    sbie
    sbbii
    @0
    @3
    vw
    vx
    @3
    vw
    nfv
    vw
    vx
    vz
    elequ1
    sbie
    3bitr3i
end
