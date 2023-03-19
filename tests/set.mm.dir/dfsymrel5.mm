include "wsymrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wal.mm"
include "dfsymrel2.mm"
include "relcnveq4.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfsymrel5
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( SymRel R <-> ( A. x A. y ( x R y <-> y R x ) /\ Rel R ) )

  proof
    cR
    wsymrel
    cR
    ccnv
    cR
    wss
    #
    cR
    wrel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @3
    @2
    cR
    wbr
    wb
    vy
    wal
    vx
    wal
    #
    @1
    wa
    cR
    dfsymrel2
    @1
    @0
    @4
    vx
    vy
    cR
    relcnveq4
    pm5.32ri
    bitri
end
