include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "dveeq1.mm"
include "com12.mm"
include "axc11r.mm"
include "aev.mm"
include "syl6.mm"
include "syl9.mm"
include "ax6evr.mm"
include "exlimiiv.mm"
include "pm2.18d.mm"

theorem axc11n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> A. y y = x )

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
    vy
    wal
    #
    vx
    vz
    weq
    #
    @0
    @1
    wn
    #
    @1
    wi
    wi
    vz
    @2
    @3
    @2
    vy
    wal
    #
    @0
    @1
    @3
    @2
    @4
    vy
    vx
    vz
    dveeq1
    com12
    @0
    @4
    @2
    vx
    wal
    @1
    @2
    vy
    vx
    axc11r
    vx
    vz
    vy
    vx
    vy
    aev
    syl6
    syl9
    vz
    vx
    ax6evr
    exlimiiv
    pm2.18d
end
