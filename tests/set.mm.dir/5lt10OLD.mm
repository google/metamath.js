include "c5.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "5lt6.mm"
include "6lt10OLD.mm"
include "5re.mm"
include "6re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 5lt10OLD



  assert |- 5 < 10

  proof
    c5
    c6
    clt
    wbr
    c6
    c10
    clt
    wbr
    c5
    c10
    clt
    wbr
    5lt6
    6lt10OLD
    c5
    c6
    c10
    5re
    6re
    10reOLD
    lttri
    mp2an
end
