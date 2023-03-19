include "c6.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "6lt7.mm"
include "7lt10OLD.mm"
include "6re.mm"
include "7re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 6lt10OLD



  assert |- 6 < 10

  proof
    c6
    c7
    clt
    wbr
    c7
    c10
    clt
    wbr
    c6
    c10
    clt
    wbr
    6lt7
    7lt10OLD
    c6
    c7
    c10
    6re
    7re
    10reOLD
    lttri
    mp2an
end
