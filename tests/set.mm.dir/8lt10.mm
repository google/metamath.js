include "c8.mm"
include "c9.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "8lt9.mm"
include "9lt10.mm"
include "8re.mm"
include "9re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 8lt10



  assert |- 8 < ; 1 0

  proof
    c8
    c9
    clt
    wbr
    c9
    c1
    cc0
    cdc
    #
    clt
    wbr
    c8
    @0
    clt
    wbr
    8lt9
    9lt10
    c8
    c9
    @0
    8re
    9re
    10re
    lttri
    mp2an
end
