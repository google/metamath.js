include "weq.mm"
include "wn.mm"
include "wel.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "pm2.24.mm"
include "sps.mm"

theorem axpowndlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( -. x = y -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) )

  proof
    vx
    vy
    weq
    #
    @0
    wn
    vx
    vy
    wel
    vz
    wex
    vx
    vz
    wel
    vy
    wal
    wi
    vx
    wal
    vy
    vx
    wel
    wi
    vy
    wal
    vx
    wex
    #
    wi
    vx
    @0
    @1
    pm2.24
    sps
end
