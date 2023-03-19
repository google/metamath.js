include "c6.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "6lt7.mm"
include "7lt8.mm"
include "6re.mm"
include "7re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 6lt8



  assert |- 6 < 8

  proof
    c6
    c7
    clt
    wbr
    c7
    c8
    clt
    wbr
    c6
    c8
    clt
    wbr
    6lt7
    7lt8
    c6
    c7
    c8
    6re
    7re
    8re
    lttri
    mp2an
end
