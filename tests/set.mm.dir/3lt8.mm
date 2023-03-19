include "c3.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "3lt4.mm"
include "4lt8.mm"
include "3re.mm"
include "4re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 3lt8



  assert |- 3 < 8

  proof
    c3
    c4
    clt
    wbr
    c4
    c8
    clt
    wbr
    c3
    c8
    clt
    wbr
    3lt4
    4lt8
    c3
    c4
    c8
    3re
    4re
    8re
    lttri
    mp2an
end
