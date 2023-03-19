include "wcel.mm"
include "crels.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "elrels2.mm"
include "df-rel.mm"
include "syl6bbr.mm"

theorem elrelsrel
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. Rels <-> Rel R ) )

  proof
    cR
    cV
    wcel
    cR
    crels
    wcel
    cR
    cvv
    cvv
    cxp
    wss
    cR
    wrel
    cR
    cV
    elrels2
    cR
    df-rel
    syl6bbr
end
