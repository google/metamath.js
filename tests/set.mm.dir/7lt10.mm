include "c7.mm"
include "c8.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "7lt8.mm"
include "8lt10.mm"
include "7re.mm"
include "8re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 7lt10



  assert |- 7 < ; 1 0

  proof
    c7
    c8
    clt
    wbr
    c8
    c1
    cc0
    cdc
    #
    clt
    wbr
    c7
    @0
    clt
    wbr
    7lt8
    8lt10
    c7
    c8
    @0
    7re
    8re
    10re
    lttri
    mp2an
end
