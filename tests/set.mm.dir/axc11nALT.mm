include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "equcomi.mm"
include "dveeq1.mm"
include "syl5com.mm"
include "axc11r.mm"
include "axc11nlemALT.mm"
include "syl6.mm"
include "syl9.mm"
include "ax6ev.mm"
include "exlimiiv.mm"
include "pm2.18d.mm"

theorem axc11nALT
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
    vz
    vx
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
    vx
    vz
    weq
    #
    vy
    wal
    #
    @0
    @1
    @2
    @4
    @3
    @5
    vz
    vx
    equcomi
    vy
    vx
    vz
    dveeq1
    syl5com
    @0
    @5
    @4
    vx
    wal
    @1
    @4
    vy
    vx
    axc11r
    vx
    vy
    vz
    axc11nlemALT
    syl6
    syl9
    vz
    vx
    ax6ev
    exlimiiv
    pm2.18d
end
