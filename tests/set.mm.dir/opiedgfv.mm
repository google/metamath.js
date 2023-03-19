include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "ciedg.mm"
include "cfv.mm"
include "c2nd.mm"
include "cvv.mm"
include "cxp.mm"
include "wceq.mm"
include "opelvvg.mm"
include "opiedgval.mm"
include "syl.mm"
include "op2ndg.mm"
include "eqtrd.mm"

theorem opiedgfv
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( V e. X /\ E e. Y ) -> ( iEdg ` <. V , E >. ) = E )

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
    cop
    #
    ciedg
    cfv
    #
    @1
    c2nd
    cfv
    #
    cE
    @0
    @1
    cvv
    cvv
    cxp
    wcel
    @2
    @3
    wceq
    cV
    cE
    cX
    cY
    opelvvg
    @1
    opiedgval
    syl
    cV
    cE
    cX
    cY
    op2ndg
    eqtrd
end
