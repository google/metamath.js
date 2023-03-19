include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "3lt4.mm"
include "4lt10OLD.mm"
include "3re.mm"
include "4re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt10OLD



  assert |- 3 < 10

  proof
    c3
    c4
    clt
    wbr
    c4
    c10
    clt
    wbr
    c3
    c10
    clt
    wbr
    3lt4
    4lt10OLD
    c3
    c4
    c10
    3re
    4re
    10reOLD
    lttri
    mp2an
end
