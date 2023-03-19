include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c5.mm"
include "3lt4.mm"
include "4lt5.mm"
include "3re.mm"
include "4re.mm"
include "5re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt5



  assert |- 3 < 5

  proof
    c3
    c4
    clt
    wbr
    c4
    c5
    clt
    wbr
    c3
    c5
    clt
    wbr
    3lt4
    4lt5
    c3
    c4
    c5
    3re
    4re
    5re
    lttri
    mp2an
end
