include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "2lt3.mm"
include "3lt9.mm"
include "2re.mm"
include "3re.mm"
include "9re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt9



  assert |- 2 < 9

  proof
    c2
    c3
    clt
    wbr
    c3
    c9
    clt
    wbr
    c2
    c9
    clt
    wbr
    2lt3
    3lt9
    c2
    c3
    c9
    2re
    3re
    9re
    lttri
    mp2an
end
