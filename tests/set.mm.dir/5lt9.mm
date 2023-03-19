include "c5.mm"
include "c6.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "5lt6.mm"
include "6lt9.mm"
include "5re.mm"
include "6re.mm"
include "9re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 5lt9



  assert |- 5 < 9

  proof
    c5
    c6
    clt
    wbr
    c6
    c9
    clt
    wbr
    c5
    c9
    clt
    wbr
    5lt6
    6lt9
    c5
    c6
    c9
    5re
    6re
    9re
    lttri
    mp2an
end
