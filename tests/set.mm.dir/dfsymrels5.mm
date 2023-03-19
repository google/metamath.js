include "cv.mm"
include "ccnv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels4.mm"
include "elrelscnveq2.mm"
include "rabimbieq.mm"

theorem dfsymrels5
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r

  disjoint r x
  disjoint r y
  disjoint x y
  assert |- SymRels = { r e. Rels | A. x A. y ( x r y <-> y r x ) }

  proof
    vr
    cv
    #
    ccnv
    @0
    wceq
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    @2
    @1
    @0
    wbr
    wb
    vy
    wal
    vx
    wal
    vr
    crels
    csymrels
    vr
    dfsymrels4
    vx
    vy
    @0
    elrelscnveq2
    rabimbieq
end
