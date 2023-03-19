include "weq.mm"
include "wal.mm"
include "axc11.mm"
include "pm2.43i.mm"
include "equcomi.mm"
include "sylg.mm"

theorem axc11n11
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> A. y y = x )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    vy
    vx
    weq
    vy
    @1
    @0
    vy
    wal
    @0
    vx
    vy
    axc11
    pm2.43i
    vx
    vy
    equcomi
    sylg
end
