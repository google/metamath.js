include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "4lt5.mm"
include "5lt10OLD.mm"
include "4re.mm"
include "5re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt10OLD



  assert |- 4 < 10

  proof
    c4
    c5
    clt
    wbr
    c5
    c10
    clt
    wbr
    c4
    c10
    clt
    wbr
    4lt5
    5lt10OLD
    c4
    c5
    c10
    4re
    5re
    10reOLD
    lttri
    mp2an
end
