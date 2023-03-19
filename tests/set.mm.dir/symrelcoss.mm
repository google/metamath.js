include "ccoss.mm"
include "wsymrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "symrelcoss2.mm"
include "dfsymrel2.mm"
include "mpbir.mm"

theorem symrelcoss
  let cR: class R


  assert |- SymRel ,~ R

  proof
    cR
    ccoss
    #
    wsymrel
    @0
    ccnv
    @0
    wss
    @0
    wrel
    wa
    cR
    symrelcoss2
    @0
    dfsymrel2
    mpbir
end
