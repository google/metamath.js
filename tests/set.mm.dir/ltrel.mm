include "clt.mm"
include "cxr.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "ltrelxr.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"

theorem ltrel



  assert |- Rel <

  proof
    clt
    cxr
    cxr
    cxp
    #
    wss
    @0
    wrel
    clt
    wrel
    ltrelxr
    cxr
    cxr
    relxp
    clt
    @0
    relss
    mp2
end
