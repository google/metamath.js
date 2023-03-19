include "c8.mm"
include "c9.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "8lt9.mm"
include "9lt10OLD.mm"
include "8re.mm"
include "9re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 8lt10OLD



  assert |- 8 < 10

  proof
    c8
    c9
    clt
    wbr
    c9
    c10
    clt
    wbr
    c8
    c10
    clt
    wbr
    8lt9
    9lt10OLD
    c8
    c9
    c10
    8re
    9re
    10reOLD
    lttri
    mp2an
end
