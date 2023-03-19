include "cv.mm"
include "ccnv.mm"
include "wss.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels2.mm"
include "cnvsym.mm"
include "rabbieq.mm"

theorem dfsymrels3
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r

  disjoint r x
  disjoint r y
  disjoint x y
  assert |- SymRels = { r e. Rels | A. x A. y ( x r y -> y r x ) }

  proof
    vr
    cv
    #
    ccnv
    @0
    wss
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
    wi
    vy
    wal
    vx
    wal
    vr
    crels
    csymrels
    vr
    dfsymrels2
    vx
    vy
    @0
    cnvsym
    rabbieq
end
