include "cnv.mm"
include "cvc.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "nvss.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"

theorem nvrel



  assert |- Rel NrmCVec

  proof
    cnv
    cvc
    cvv
    cxp
    #
    wss
    @0
    wrel
    cnv
    wrel
    nvss
    cvc
    cvv
    relxp
    cnv
    @0
    relss
    mp2
end
