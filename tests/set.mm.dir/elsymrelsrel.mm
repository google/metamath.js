include "wcel.mm"
include "ccnv.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "wrel.mm"
include "csymrels.mm"
include "wsymrel.mm"
include "elrelsrel.mm"
include "anbi2d.mm"
include "elsymrels2.mm"
include "dfsymrel2.mm"
include "3bitr4g.mm"

theorem elsymrelsrel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. SymRels <-> SymRel R ) )

  proof
    cR
    cV
    wcel
    #
    cR
    ccnv
    cR
    wss
    #
    cR
    crels
    wcel
    #
    wa
    @1
    cR
    wrel
    #
    wa
    cR
    csymrels
    wcel
    cR
    wsymrel
    @0
    @2
    @3
    @1
    cR
    cV
    elrelsrel
    anbi2d
    cR
    elsymrels2
    cR
    dfsymrel2
    3bitr4g
end
