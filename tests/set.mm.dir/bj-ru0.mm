include "wel.mm"
include "wn.mm"
include "wb.mm"
include "wal.mm"
include "pm5.19.mm"
include "weq.mm"
include "elequ1.mm"
include "bj-elequ12.mm"
include "anidms.mm"
include "notbid.mm"
include "bibi12d.mm"
include "bj-spvv.mm"
include "mto.mm"

theorem bj-ru0
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- -. A. x ( x e. y <-> -. x e. x )

  proof
    vx
    vy
    wel
    #
    vx
    vx
    wel
    #
    wn
    #
    wb
    #
    vx
    wal
    vy
    vy
    wel
    #
    @4
    wn
    #
    wb
    #
    @4
    pm5.19
    @3
    @6
    vx
    vy
    vx
    vy
    weq
    #
    @0
    @4
    @2
    @5
    vx
    vy
    vy
    elequ1
    @7
    @1
    @4
    @7
    @1
    @4
    wb
    vx
    vy
    vx
    vy
    bj-elequ12
    anidms
    notbid
    bibi12d
    bj-spvv
    mto
end
