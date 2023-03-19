include "wcel.mm"
include "wa.mm"
include "cvtx.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "opvtxfv.mm"
include "eqtrd.mm"

theorem opvtxov
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( V e. X /\ E e. Y ) -> ( V Vtx E ) = V )

  proof
    cV
    cX
    wcel
    cE
    cY
    wcel
    wa
    #
    cV
    cE
    cvtx
    co
    #
    cV
    cE
    cop
    cvtx
    cfv
    #
    cV
    @1
    @2
    wceq
    @0
    cV
    cE
    cvtx
    df-ov
    a1i
    cE
    cV
    cX
    cY
    opvtxfv
    eqtrd
end
