include "c4.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "4lt5.mm"
include "5lt9.mm"
include "4re.mm"
include "5re.mm"
include "9re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 4lt9



  assert |- 4 < 9

  proof
    c4
    c5
    clt
    wbr
    c5
    c9
    clt
    wbr
    c4
    c9
    clt
    wbr
    4lt5
    5lt9
    c4
    c5
    c9
    4re
    5re
    9re
    lttri
    mp2an
end
