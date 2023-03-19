include "wceq.mm"
include "csn.mm"
include "cop.mm"
include "ciedg.mm"
include "cfv.mm"
include "eqid.mm"
include "funsneqopsn.mm"
include "fveq2.mm"
include "snex.mm"
include "opiedgfvi.mm"
include "syl6eq.mm"
include "mp2b.mm"

theorem iedgvalsnop
  let cB: class B
  let cG: class G
  assume vtxvalsnop.b: |- B e. _V
  assume vtxvalsnop.g: |- G = { <. B , B >. }


  assert |- ( iEdg ` G ) = { B }

  proof
    cB
    cB
    wceq
    cG
    cB
    csn
    #
    @0
    cop
    #
    wceq
    #
    cG
    ciedg
    cfv
    #
    @0
    wceq
    cB
    eqid
    cB
    cB
    cG
    vtxvalsnop.b
    vtxvalsnop.b
    vtxvalsnop.g
    funsneqopsn
    @2
    @3
    @1
    ciedg
    cfv
    @0
    cG
    @1
    ciedg
    fveq2
    @0
    @0
    cB
    snex
    #
    @4
    opiedgfvi
    syl6eq
    mp2b
end
