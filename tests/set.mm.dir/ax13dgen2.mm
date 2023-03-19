include "weq.mm"
include "wn.mm"
include "wal.mm"
include "equcomi.mm"
include "pm2.21.mm"
include "syl5.mm"

theorem ax13dgen2
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. x = y -> ( y = x -> A. x y = x ) )

  proof
    vy
    vx
    weq
    #
    vx
    vy
    weq
    #
    @1
    wn
    @0
    vx
    wal
    #
    vy
    vx
    equcomi
    @1
    @2
    pm2.21
    syl5
end
