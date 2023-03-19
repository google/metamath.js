include "weq.mm"
include "wn.mm"
include "wal.mm"
include "ax6fromc10.mm"
include "ax7.mm"
include "pm2.43i.mm"
include "con3i.mm"
include "alimi.mm"
include "mto.mm"

theorem equidqe
  let vx: setvar x
  let vy: setvar y


  assert |- -. A. y -. x = x

  proof
    vx
    vx
    weq
    #
    wn
    #
    vy
    wal
    vy
    vx
    weq
    #
    wn
    #
    vy
    wal
    vy
    vx
    ax6fromc10
    @1
    @3
    vy
    @2
    @0
    @2
    @0
    vy
    vx
    vx
    ax7
    pm2.43i
    con3i
    alimi
    mto
end
