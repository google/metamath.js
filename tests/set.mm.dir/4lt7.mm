include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "4lt5.mm"
include "5lt7.mm"
include "4re.mm"
include "5re.mm"
include "7re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt7



  assert |- 4 < 7

  proof
    c4
    c5
    clt
    wbr
    c5
    c7
    clt
    wbr
    c4
    c7
    clt
    wbr
    4lt5
    5lt7
    c4
    c5
    c7
    4re
    5re
    7re
    lttri
    mp2an
end
