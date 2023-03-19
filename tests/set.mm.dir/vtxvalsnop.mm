include "wceq.mm"
include "csn.mm"
include "cop.mm"
include "cvtx.mm"
include "cfv.mm"
include "eqid.mm"
include "funsneqopsn.mm"
include "fveq2.mm"
include "snex.mm"
include "opvtxfvi.mm"
include "syl6eq.mm"
include "mp2b.mm"

theorem vtxvalsnop
  let cB: class B
  let cG: class G
  assume vtxvalsnop.b: |- B e. _V
  assume vtxvalsnop.g: |- G = { <. B , B >. }


  assert |- ( Vtx ` G ) = { B }

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
    cvtx
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
    cvtx
    cfv
    @0
    cG
    @1
    cvtx
    fveq2
    @0
    @0
    cB
    snex
    #
    @4
    opvtxfvi
    syl6eq
    mp2b
end
