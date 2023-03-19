include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wb.mm"
include "sp.mm"
include "aev.mm"
include "pm2.21.mm"
include "impbid2.mm"
include "anim12i.mm"
include "wl-aleq.mm"
include "sylibr.mm"

theorem wl-ax11-lem2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- ( ( A. u u = y /\ -. A. x x = y ) -> A. x u = y )

  proof
    vu
    vy
    weq
    #
    vu
    wal
    #
    vx
    vy
    weq
    vx
    wal
    #
    wn
    #
    wa
    @0
    vx
    vu
    weq
    vx
    wal
    #
    @2
    wb
    #
    wa
    @0
    vx
    wal
    @1
    @0
    @3
    @5
    @0
    vu
    sp
    @3
    @4
    @2
    vx
    vu
    vx
    vy
    vx
    aev
    @2
    @4
    pm2.21
    impbid2
    anim12i
    vx
    vu
    vy
    wl-aleq
    sylibr
end
