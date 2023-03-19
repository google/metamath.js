include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "2lt3.mm"
include "3lt7.mm"
include "2re.mm"
include "3re.mm"
include "7re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt7



  assert |- 2 < 7

  proof
    c2
    c3
    clt
    wbr
    c3
    c7
    clt
    wbr
    c2
    c7
    clt
    wbr
    2lt3
    3lt7
    c2
    c3
    c7
    2re
    3re
    7re
    lttri
    mp2an
end
