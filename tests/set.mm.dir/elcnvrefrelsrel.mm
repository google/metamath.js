include "wcel.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "crels.mm"
include "wa.mm"
include "wrel.mm"
include "ccnvrefrels.mm"
include "wcnvrefrel.mm"
include "elrelsrel.mm"
include "anbi2d.mm"
include "elcnvrefrels2.mm"
include "dfcnvrefrel2.mm"
include "3bitr4g.mm"

theorem elcnvrefrelsrel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. CnvRefRels <-> CnvRefRel R ) )

  proof
    cR
    cV
    wcel
    #
    cR
    cid
    cR
    cdm
    cR
    crn
    cxp
    cin
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
    ccnvrefrels
    wcel
    cR
    wcnvrefrel
    @0
    @2
    @3
    @1
    cR
    cV
    elrelsrel
    anbi2d
    cR
    elcnvrefrels2
    cR
    dfcnvrefrel2
    3bitr4g
end
