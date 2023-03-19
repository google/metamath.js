include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "edgval.mm"
include "opiedgfv.mm"
include "rneqd.mm"
include "syl5eq.mm"

theorem edgopval
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( V e. W /\ E e. X ) -> ( Edg ` <. V , E >. ) = ran E )

  proof
    cV
    cW
    wcel
    cE
    cX
    wcel
    wa
    #
    cV
    cE
    cop
    #
    cedg
    cfv
    @1
    ciedg
    cfv
    #
    crn
    cE
    crn
    @1
    edgval
    @0
    @2
    cE
    cE
    cV
    cW
    cX
    opiedgfv
    rneqd
    syl5eq
end
