include "wcel.mm"
include "crels.mm"
include "wrel.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "wceq.mm"
include "elrelsrel.mm"
include "dfrel6.mm"
include "syl6bb.mm"

theorem elrels6
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. Rels <-> ( R i^i ( dom R X. ran R ) ) = R ) )

  proof
    cR
    cV
    wcel
    cR
    crels
    wcel
    cR
    wrel
    cR
    cR
    cdm
    cR
    crn
    cxp
    cin
    cR
    wceq
    cR
    cV
    elrelsrel
    cR
    dfrel6
    syl6bb
end
