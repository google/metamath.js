include "c6.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "6lt7.mm"
include "7lt10.mm"
include "6re.mm"
include "7re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 6lt10



  assert |- 6 < ; 1 0

  proof
    c6
    c7
    clt
    wbr
    c7
    c1
    cc0
    cdc
    #
    clt
    wbr
    c6
    @0
    clt
    wbr
    6lt7
    7lt10
    c6
    c7
    @0
    6re
    7re
    10re
    lttri
    mp2an
end
