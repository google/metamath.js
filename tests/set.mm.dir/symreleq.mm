include "wceq.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "wsymrel.mm"
include "cnveq.mm"
include "id.mm"
include "sseq12d.mm"
include "releq.mm"
include "anbi12d.mm"
include "dfsymrel2.mm"
include "3bitr4g.mm"

theorem symreleq
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( SymRel R <-> SymRel S ) )

  proof
    cR
    cS
    wceq
    #
    cR
    ccnv
    #
    cR
    wss
    #
    cR
    wrel
    #
    wa
    cS
    ccnv
    #
    cS
    wss
    #
    cS
    wrel
    #
    wa
    cR
    wsymrel
    cS
    wsymrel
    @0
    @2
    @5
    @3
    @6
    @0
    @1
    @4
    cR
    cS
    cR
    cS
    cnveq
    @0
    id
    sseq12d
    cR
    cS
    releq
    anbi12d
    cR
    dfsymrel2
    cS
    dfsymrel2
    3bitr4g
end
