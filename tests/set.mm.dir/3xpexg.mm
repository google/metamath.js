include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "xpexg.mm"
include "anidms.mm"
include "mpancom.mm"

theorem 3xpexg
  let cV: class V
  let cW: class W


  assert |- ( V e. W -> ( ( V X. V ) X. V ) e. _V )

  proof
    cV
    cV
    cxp
    #
    cvv
    wcel
    #
    cV
    cW
    wcel
    #
    @0
    cV
    cxp
    cvv
    wcel
    @2
    @1
    cV
    cV
    cW
    cW
    xpexg
    anidms
    @0
    cV
    cvv
    cW
    xpexg
    mpancom
end
