include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wi.mm"
include "nfae.mm"
include "simpl.mm"
include "alimi.mm"
include "nd1.mm"
include "pm2.21d.mm"
include "syl5.mm"
include "alrimi.mm"
include "19.8a.mm"
include "syl.mm"

theorem axacndlem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x x = y -> E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vy
    vz
    wel
    #
    vz
    vw
    wel
    #
    wa
    #
    vx
    wal
    #
    @3
    vy
    vw
    wel
    vw
    vx
    wel
    wa
    wa
    vw
    wex
    vy
    vw
    weq
    wb
    vy
    wal
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    @8
    vx
    wex
    @0
    @7
    vy
    vx
    vy
    vy
    nfae
    @0
    @6
    vz
    vx
    vy
    vz
    nfae
    @4
    @1
    vx
    wal
    #
    @0
    @5
    @3
    @1
    vx
    @1
    @2
    simpl
    alimi
    @0
    @9
    @5
    vx
    vy
    vz
    nd1
    pm2.21d
    syl5
    alrimi
    alrimi
    @8
    vx
    19.8a
    syl
end
