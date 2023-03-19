include "weq.mm"
include "wal.mm"
include "cbvaev.mm"
include "equequ2.mm"
include "biimprd.mm"
include "al2imi.mm"
include "syl5com.mm"
include "wn.mm"
include "dveeq1.mm"
include "spsd.mm"
include "com12.mm"
include "con1d.mm"
include "pm2.61d.mm"

theorem axc11nlemALT
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w

  disjoint w x
  disjoint w y
  assert |- ( A. x x = w -> A. y y = x )

  proof
    vx
    vw
    weq
    #
    vx
    wal
    #
    @0
    vy
    wal
    #
    vy
    vx
    weq
    #
    vy
    wal
    #
    @1
    vy
    vw
    weq
    #
    vy
    wal
    @2
    @4
    vx
    vw
    vy
    cbvaev
    @0
    @5
    @3
    vy
    @0
    @3
    @5
    vx
    vw
    vy
    equequ2
    biimprd
    al2imi
    syl5com
    @1
    @4
    @2
    @4
    wn
    #
    @1
    @2
    @6
    @0
    @2
    vx
    vy
    vx
    vw
    dveeq1
    spsd
    com12
    con1d
    pm2.61d
end
