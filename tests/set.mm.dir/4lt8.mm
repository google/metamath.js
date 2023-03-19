include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "4lt5.mm"
include "5lt8.mm"
include "4re.mm"
include "5re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt8



  assert |- 4 < 8

  proof
    c4
    c5
    clt
    wbr
    c5
    c8
    clt
    wbr
    c4
    c8
    clt
    wbr
    4lt5
    5lt8
    c4
    c5
    c8
    4re
    5re
    8re
    lttri
    mp2an
end
