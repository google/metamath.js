include "cv.mm"
include "ccnv.mm"
include "wceq.mm"
include "crels.mm"
include "csymrels.mm"
include "dfsymrels4.mm"
include "cnveq.mm"
include "id.mm"
include "eqeq12d.mm"
include "rabeqel.mm"

theorem elsymrels4
  let cR: class R
  let vr: setvar r


  assert |- ( R e. SymRels <-> ( `' R = R /\ R e. Rels ) )

  proof
    vr
    cv
    #
    ccnv
    #
    @0
    wceq
    cR
    ccnv
    #
    cR
    wceq
    vr
    crels
    csymrels
    cR
    vr
    dfsymrels4
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
    eqeq12d
    rabeqel
end
