include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "3lt4.mm"
include "4lt6.mm"
include "3re.mm"
include "4re.mm"
include "6re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt6



  assert |- 3 < 6

  proof
    c3
    c4
    clt
    wbr
    c4
    c6
    clt
    wbr
    c3
    c6
    clt
    wbr
    3lt4
    4lt6
    c3
    c4
    c6
    3re
    4re
    6re
    lttri
    mp2an
end
