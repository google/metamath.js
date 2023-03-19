include "c6.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "6lt7.mm"
include "7lt9.mm"
include "6re.mm"
include "7re.mm"
include "9re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 6lt9



  assert |- 6 < 9

  proof
    c6
    c7
    clt
    wbr
    c7
    c9
    clt
    wbr
    c6
    c9
    clt
    wbr
    6lt7
    7lt9
    c6
    c7
    c9
    6re
    7re
    9re
    lttri
    mp2an
end
