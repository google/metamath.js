include "cv.mm"
include "ccnv.mm"
include "wss.mm"
include "wceq.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels2.mm"
include "elrelscnveq.mm"
include "rabimbieq.mm"

theorem dfsymrels4
  let vr: setvar r


  assert |- SymRels = { r e. Rels | `' r = r }

  proof
    vr
    cv
    #
    ccnv
    #
    @0
    wss
    @1
    @0
    wceq
    vr
    crels
    csymrels
    vr
    dfsymrels2
    @0
    elrelscnveq
    rabimbieq
end
