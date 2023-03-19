include "cv.mm"
include "ccnv.mm"
include "wss.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels2.mm"
include "wceq.mm"
include "cnveq.mm"
include "id.mm"
include "sseq12d.mm"
include "rabeqel.mm"

theorem elsymrels2
  let cR: class R
  let vr: setvar r


  assert |- ( R e. SymRels <-> ( `' R C_ R /\ R e. Rels ) )

  proof
    vr
    cv
    #
    ccnv
    #
    @0
    wss
    cR
    ccnv
    #
    cR
    wss
    vr
    crels
    csymrels
    cR
    vr
    dfsymrels2
    @0
    cR
    wceq
    #
    @1
    @2
    @0
    cR
    @0
    cR
    cnveq
    @3
    id
    sseq12d
    rabeqel
end
