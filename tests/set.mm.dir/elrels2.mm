include "crels.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "df-rels.mm"
include "eleq2i.mm"
include "elpwg.mm"
include "syl5bb.mm"

theorem elrels2
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( R e. Rels <-> R C_ ( _V X. _V ) ) )

  proof
    cR
    crels
    wcel
    cR
    cvv
    cvv
    cxp
    #
    cpw
    #
    wcel
    cR
    cV
    wcel
    cR
    @0
    wss
    crels
    @1
    cR
    df-rels
    eleq2i
    cR
    @0
    cV
    elpwg
    syl5bb
end
