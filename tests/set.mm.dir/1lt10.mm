include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cdc.mm"
include "1lt2.mm"
include "2lt10.mm"
include "1re.mm"
include "2re.mm"
include "10re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt10



  assert |- 1 < ; 1 0

  proof
    c1
    c2
    clt
    wbr
    c2
    c1
    cc0
    cdc
    #
    clt
    wbr
    c1
    @0
    clt
    wbr
    1lt2
    2lt10
    c1
    c2
    @0
    1re
    2re
    10re
    lttri
    mp2an
end
