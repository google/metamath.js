include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "opvtxfv.mm"
include "mp2an.mm"

theorem opvtxfvi
  let cE: class E
  let cV: class V
  assume opvtxfvi.v: |- V e. _V
  assume opvtxfvi.e: |- E e. _V


  assert |- ( Vtx ` <. V , E >. ) = V

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
    cvtx
    cfv
    cV
    wceq
    opvtxfvi.v
    opvtxfvi.e
    cE
    cV
    cvv
    cvv
    opvtxfv
    mp2an
end
