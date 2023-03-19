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
include "nd3.mm"
include "pm2.21d.mm"
include "syl5.mm"
include "alrimi.mm"
include "axc4i.mm"
include "19.8a.mm"
include "syl.mm"

theorem axacndlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. y y = z -> E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) )

  proof
    vy
    vz
    weq
    #
    vy
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
    @4
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
    @9
    vx
    wex
    @0
    @8
    vy
    @1
    @7
    vz
    vy
    vz
    vz
    nfae
    @5
    @2
    vx
    wal
    #
    @1
    @6
    @4
    @2
    vx
    @2
    @3
    simpl
    alimi
    @1
    @10
    @6
    vy
    vz
    vx
    nd3
    pm2.21d
    syl5
    alrimi
    axc4i
    @9
    vx
    19.8a
    syl
end
