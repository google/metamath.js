include "weq.mm"
include "wal.mm"
include "axc11n.mm"
include "axc4i.mm"
include "syl.mm"

theorem wl-hbae1
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x x = y -> A. y A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vy
    vx
    weq
    #
    vy
    wal
    @0
    vy
    wal
    vx
    vy
    axc11n
    @1
    @0
    vy
    vy
    vx
    axc11n
    axc4i
    syl
end
