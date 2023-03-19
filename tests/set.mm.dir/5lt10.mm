include "c5.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "5lt6.mm"
include "6lt10.mm"
include "5re.mm"
include "6re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 5lt10



  assert |- 5 < ; 1 0

  proof
    c5
    c6
    clt
    wbr
    c6
    c1
    cc0
    cdc
    #
    clt
    wbr
    c5
    @0
    clt
    wbr
    5lt6
    6lt10
    c5
    c6
    @0
    5re
    6re
    10re
    lttri
    mp2an
end
