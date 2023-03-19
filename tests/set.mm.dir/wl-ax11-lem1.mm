include "weq.mm"
include "wal.mm"
include "wl-aetr.mm"
include "wi.mm"
include "aecoms.mm"
include "impbid.mm"

theorem wl-ax11-lem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( A. x x = z <-> A. y y = z ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vx
    vz
    weq
    vx
    wal
    #
    vy
    vz
    weq
    vy
    wal
    #
    vx
    vy
    vz
    wl-aetr
    @1
    @0
    wi
    vy
    vx
    vy
    vx
    vz
    wl-aetr
    aecoms
    impbid
end
