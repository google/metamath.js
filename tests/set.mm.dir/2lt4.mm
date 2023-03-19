include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c4.mm"
include "2lt3.mm"
include "3lt4.mm"
include "2re.mm"
include "3re.mm"
include "4re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt4



  assert |- 2 < 4

  proof
    c2
    c3
    clt
    wbr
    c3
    c4
    clt
    wbr
    c2
    c4
    clt
    wbr
    2lt3
    3lt4
    c2
    c3
    c4
    2re
    3re
    4re
    lttri
    mp2an
end
