include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels5.mm"
include "wceq.mm"
include "breq.mm"
include "bibi12d.mm"
include "2albidv.mm"
include "rabeqel.mm"

theorem elsymrels5
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vr: setvar r

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint R r
  disjoint r x
  disjoint r y
  assert |- ( R e. SymRels <-> ( A. x A. y ( x R y <-> y R x ) /\ R e. Rels ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    vr
    cv
    #
    wbr
    #
    @1
    @0
    @2
    wbr
    #
    wb
    #
    vy
    wal
    vx
    wal
    @0
    @1
    cR
    wbr
    #
    @1
    @0
    cR
    wbr
    #
    wb
    #
    vy
    wal
    vx
    wal
    vr
    crels
    csymrels
    cR
    vx
    vy
    vr
    dfsymrels5
    @2
    cR
    wceq
    #
    @5
    @8
    vx
    vy
    @9
    @3
    @6
    @4
    @7
    @0
    @1
    @2
    cR
    breq
    @1
    @0
    @2
    cR
    breq
    bibi12d
    2albidv
    rabeqel
end
