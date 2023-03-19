include "wsymrel.mm"
include "cdm.mm"
include "ccnv.mm"
include "crn.mm"
include "rncnv.mm"
include "wceq.mm"
include "wrel.mm"
include "dfsymrel4.mm"
include "simplbi.mm"
include "rneqd.mm"
include "syl5eqr.mm"

theorem symrelim
  let cR: class R


  assert |- ( SymRel R -> dom R = ran R )

  proof
    cR
    wsymrel
    #
    cR
    cdm
    cR
    ccnv
    #
    crn
    cR
    crn
    cR
    rncnv
    @0
    @1
    cR
    @0
    @1
    cR
    wceq
    cR
    wrel
    cR
    dfsymrel4
    simplbi
    rneqd
    syl5eqr
end
