include "wcel.mm"
include "crels.mm"
include "wrel.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "elrelsrel.mm"
include "dfrel5.mm"
include "syl6bb.mm"

theorem elrels5
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. Rels <-> ( R |` dom R ) = R ) )

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
    cres
    cR
    wceq
    cR
    cV
    elrelsrel
    cR
    dfrel5
    syl6bb
end
