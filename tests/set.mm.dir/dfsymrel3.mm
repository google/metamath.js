include "wsymrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "dfsymrel2.mm"
include "cnvsym.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem dfsymrel3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( SymRel R <-> ( A. x A. y ( x R y -> y R x ) /\ Rel R ) )

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
    wi
    vy
    wal
    vx
    wal
    #
    @1
    wa
    cR
    dfsymrel2
    @0
    @4
    @1
    vx
    vy
    cR
    cnvsym
    anbi1i
    bitri
end
