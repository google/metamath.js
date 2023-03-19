include "weq.mm"
include "wsb.mm"
include "equsb3lem.mm"
include "sbbii.mm"
include "nfv.mm"
include "sbco2.mm"
include "3bitr3i.mm"

theorem equsb3ALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint y z
  disjoint w y
  disjoint w z
  disjoint w x
  assert |- ( [ x / y ] y = z <-> x = z )

  proof
    vy
    vz
    weq
    #
    vy
    vw
    wsb
    #
    vw
    vx
    wsb
    vw
    vz
    weq
    #
    vw
    vx
    wsb
    @0
    vy
    vx
    wsb
    vx
    vz
    weq
    @1
    @2
    vw
    vx
    vw
    vy
    vz
    equsb3lem
    sbbii
    @0
    vy
    vx
    vw
    @0
    vw
    nfv
    sbco2
    vx
    vw
    vz
    equsb3lem
    3bitr3i
end
