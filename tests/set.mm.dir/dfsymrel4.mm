include "wsymrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "wceq.mm"
include "dfsymrel2.mm"
include "relcnveq.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem dfsymrel4
  let cR: class R


  assert |- ( SymRel R <-> ( `' R = R /\ Rel R ) )

  proof
    cR
    wsymrel
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
    @0
    cR
    wceq
    #
    @2
    wa
    cR
    dfsymrel2
    @2
    @1
    @3
    cR
    relcnveq
    pm5.32ri
    bitri
end
