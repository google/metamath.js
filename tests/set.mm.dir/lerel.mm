include "cle.mm"
include "cxr.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "lerelxr.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"

theorem lerel



  assert |- Rel <_

  proof
    cle
    cxr
    cxr
    cxp
    #
    wss
    @0
    wrel
    cle
    wrel
    lerelxr
    cxr
    cxr
    relxp
    cle
    @0
    relss
    mp2
end
