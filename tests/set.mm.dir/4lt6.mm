include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "4lt5.mm"
include "5lt6.mm"
include "4re.mm"
include "5re.mm"
include "6re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt6



  assert |- 4 < 6

  proof
    c4
    c5
    clt
    wbr
    c5
    c6
    clt
    wbr
    c4
    c6
    clt
    wbr
    4lt5
    5lt6
    c4
    c5
    c6
    4re
    5re
    6re
    lttri
    mp2an
end
