include "c1.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c5.mm"
include "1lt4.mm"
include "4lt5.mm"
include "1re.mm"
include "4re.mm"
include "5re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt5



  assert |- 1 < 5

  proof
    c1
    c4
    clt
    wbr
    c4
    c5
    clt
    wbr
    c1
    c5
    clt
    wbr
    1lt4
    4lt5
    c1
    c4
    c5
    1re
    4re
    5re
    lttri
    mp2an
end
