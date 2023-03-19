include "c5.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "5lt6.mm"
include "6lt7.mm"
include "5re.mm"
include "6re.mm"
include "7re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 5lt7



  assert |- 5 < 7

  proof
    c5
    c6
    clt
    wbr
    c6
    c7
    clt
    wbr
    c5
    c7
    clt
    wbr
    5lt6
    6lt7
    c5
    c6
    c7
    5re
    6re
    7re
    lttri
    mp2an
end
