include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "3lt4.mm"
include "4lt10.mm"
include "3re.mm"
include "4re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt10



  assert |- 3 < ; 1 0

  proof
    c3
    c4
    clt
    wbr
    c4
    c1
    cc0
    cdc
    #
    clt
    wbr
    c3
    @0
    clt
    wbr
    3lt4
    4lt10
    c3
    c4
    @0
    3re
    4re
    10re
    lttri
    mp2an
end
