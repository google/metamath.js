include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "4lt5.mm"
include "5lt10.mm"
include "4re.mm"
include "5re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt10



  assert |- 4 < ; 1 0

  proof
    c4
    c5
    clt
    wbr
    c5
    c1
    cc0
    cdc
    #
    clt
    wbr
    c4
    @0
    clt
    wbr
    4lt5
    5lt10
    c4
    c5
    @0
    4re
    5re
    10re
    lttri
    mp2an
end
