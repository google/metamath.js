include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "ciedg.mm"
include "cfv.mm"
include "wceq.mm"
include "opiedgfv.mm"
include "mp2an.mm"

theorem opiedgfvi
  let cE: class E
  let cV: class V
  assume opvtxfvi.v: |- V e. _V
  assume opvtxfvi.e: |- E e. _V


  assert |- ( iEdg ` <. V , E >. ) = E

  proof
    cV
    cvv
    wcel
    cE
    cvv
    wcel
    cV
    cE
    cop
    ciedg
    cfv
    cE
    wceq
    opvtxfvi.v
    opvtxfvi.e
    cE
    cV
    cvv
    cvv
    opiedgfv
    mp2an
end
