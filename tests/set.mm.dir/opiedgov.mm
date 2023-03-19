include "wcel.mm"
include "wa.mm"
include "ciedg.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "opiedgfv.mm"
include "eqtrd.mm"

theorem opiedgov
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( V e. X /\ E e. Y ) -> ( V iEdg E ) = E )

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
    ciedg
    co
    #
    cV
    cE
    cop
    ciedg
    cfv
    #
    cE
    @1
    @2
    wceq
    @0
    cV
    cE
    ciedg
    df-ov
    a1i
    cE
    cV
    cX
    cY
    opiedgfv
    eqtrd
end
