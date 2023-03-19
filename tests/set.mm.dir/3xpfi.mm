include "cxp.mm"
include "cfn.mm"
include "wcel.mm"
include "xpfi.mm"
include "anidms.mm"
include "mpancom.mm"

theorem 3xpfi
  let cV: class V


  assert |- ( V e. Fin -> ( ( V X. V ) X. V ) e. Fin )

  proof
    cV
    cV
    cxp
    #
    cfn
    wcel
    #
    cV
    cfn
    wcel
    #
    @0
    cV
    cxp
    cfn
    wcel
    @2
    @1
    cV
    cV
    xpfi
    anidms
    @0
    cV
    xpfi
    mpancom
end
