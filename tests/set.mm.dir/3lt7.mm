include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "3lt4.mm"
include "4lt7.mm"
include "3re.mm"
include "4re.mm"
include "7re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt7



  assert |- 3 < 7

  proof
    c3
    c4
    clt
    wbr
    c4
    c7
    clt
    wbr
    c3
    c7
    clt
    wbr
    3lt4
    4lt7
    c3
    c4
    c7
    3re
    4re
    7re
    lttri
    mp2an
end
