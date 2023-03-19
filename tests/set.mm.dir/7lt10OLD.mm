include "c7.mm"
include "c8.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "7lt8.mm"
include "8lt10OLD.mm"
include "7re.mm"
include "8re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 7lt10OLD



  assert |- 7 < 10

  proof
    c7
    c8
    clt
    wbr
    c8
    c10
    clt
    wbr
    c7
    c10
    clt
    wbr
    7lt8
    8lt10OLD
    c7
    c8
    c10
    7re
    8re
    10reOLD
    lttri
    mp2an
end
