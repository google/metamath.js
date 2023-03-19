include "wcel.mm"
include "wa.mm"
include "cedg.mm"
include "co.mm"
include "cop.mm"
include "cfv.mm"
include "crn.mm"
include "df-ov.mm"
include "edgopval.mm"
include "syl5eq.mm"

theorem edgov
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( V e. W /\ E e. X ) -> ( V Edg E ) = ran E )

  proof
    cV
    cW
    wcel
    cE
    cX
    wcel
    wa
    cV
    cE
    cedg
    co
    cV
    cE
    cop
    cedg
    cfv
    cE
    crn
    cV
    cE
    cedg
    df-ov
    cE
    cV
    cW
    cX
    edgopval
    syl5eq
end
