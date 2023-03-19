include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "2lt3.mm"
include "3lt10OLD.mm"
include "2re.mm"
include "3re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt10OLD



  assert |- 2 < 10

  proof
    c2
    c3
    clt
    wbr
    c3
    c10
    clt
    wbr
    c2
    c10
    clt
    wbr
    2lt3
    3lt10OLD
    c2
    c3
    c10
    2re
    3re
    10reOLD
    lttri
    mp2an
end
