include "weq.mm"
include "wsb.mm"
include "equsb3lem.mm"
include "sbbii.mm"
include "sbcom3.mm"
include "nfv.mm"
include "sbf.mm"
include "bitri.mm"
include "3bitr3i.mm"

theorem equsb3
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
    #
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
    #
    vx
    vz
    weq
    @1
    @3
    vw
    vx
    vw
    vy
    vz
    equsb3lem
    sbbii
    @2
    @4
    vw
    vx
    wsb
    @4
    @0
    vy
    vw
    vx
    sbcom3
    @4
    vw
    vx
    @4
    vw
    nfv
    sbf
    bitri
    vx
    vw
    vz
    equsb3lem
    3bitr3i
end
