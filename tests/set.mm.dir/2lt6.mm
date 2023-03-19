include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "2lt3.mm"
include "3lt6.mm"
include "2re.mm"
include "3re.mm"
include "6re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt6



  assert |- 2 < 6

  proof
    c2
    c3
    clt
    wbr
    c3
    c6
    clt
    wbr
    c2
    c6
    clt
    wbr
    2lt3
    3lt6
    c2
    c3
    c6
    2re
    3re
    6re
    lttri
    mp2an
end
