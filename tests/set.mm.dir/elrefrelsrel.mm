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
include "crefrels.mm"
include "wrefrel.mm"
include "elrelsrel.mm"
include "anbi2d.mm"
include "elrefrels2.mm"
include "dfrefrel2.mm"
include "3bitr4g.mm"

theorem elrefrelsrel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. RefRels <-> RefRel R ) )

  proof
    cR
    cV
    wcel
    #
    cid
    cR
    cdm
    cR
    crn
    cxp
    cin
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
    crefrels
    wcel
    cR
    wrefrel
    @0
    @2
    @3
    @1
    cR
    cV
    elrelsrel
    anbi2d
    cR
    elrefrels2
    cR
    dfrefrel2
    3bitr4g
end
