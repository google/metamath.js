include "wcel.mm"
include "c0.mm"
include "cop.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "ciedg.mm"
include "cfv.mm"
include "wceq.mm"
include "0ex.mm"
include "opiedgfv.mm"
include "mpan2.mm"
include "usgr0e.mm"

theorem usgr0eop
  let cV: class V
  let cW: class W


  assert |- ( V e. W -> <. V , (/) >. e. USGraph )

  proof
    cV
    cW
    wcel
    #
    cV
    c0
    cop
    #
    cvv
    @1
    cvv
    wcel
    @0
    cV
    c0
    opex
    a1i
    @0
    c0
    cvv
    wcel
    @1
    ciedg
    cfv
    c0
    wceq
    0ex
    c0
    cV
    cW
    cvv
    opiedgfv
    mpan2
    usgr0e
end
