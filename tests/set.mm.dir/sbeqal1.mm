include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wsb.mm"
include "sb2.mm"
include "equsb3.mm"
include "sylib.mm"

theorem sbeqal1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( A. x ( x = y -> x = z ) -> y = z )

  proof
    vx
    vy
    weq
    vx
    vz
    weq
    #
    wi
    vx
    wal
    @0
    vx
    vy
    wsb
    vy
    vz
    weq
    @0
    vx
    vy
    sb2
    vy
    vx
    vz
    equsb3
    sylib
end
