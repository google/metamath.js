include "c5.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "5lt6.mm"
include "6lt8.mm"
include "5re.mm"
include "6re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 5lt8



  assert |- 5 < 8

  proof
    c5
    c6
    clt
    wbr
    c6
    c8
    clt
    wbr
    c5
    c8
    clt
    wbr
    5lt6
    6lt8
    c5
    c6
    c8
    5re
    6re
    8re
    lttri
    mp2an
end
