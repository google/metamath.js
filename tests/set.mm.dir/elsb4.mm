include "wel.mm"
include "wsb.mm"
include "nfv.mm"
include "sbco2.mm"
include "elequ2.mm"
include "sbie.mm"
include "sbbii.mm"
include "3bitr3i.mm"

theorem elsb4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w y
  disjoint w z
  disjoint w x
  assert |- ( [ x / y ] z e. y <-> z e. x )

  proof
    vz
    vw
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
    vz
    vy
    wel
    #
    vy
    vx
    wsb
    vz
    vx
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
    elequ2
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
    elequ2
    sbie
    3bitr3i
end
