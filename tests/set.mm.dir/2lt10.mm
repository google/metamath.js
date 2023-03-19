include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "2lt3.mm"
include "3lt10.mm"
include "2re.mm"
include "3re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt10



  assert |- 2 < ; 1 0

  proof
    c2
    c3
    clt
    wbr
    c3
    c1
    cc0
    cdc
    #
    clt
    wbr
    c2
    @0
    clt
    wbr
    2lt3
    3lt10
    c2
    c3
    @0
    2re
    3re
    10re
    lttri
    mp2an
end
