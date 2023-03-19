include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "2lt3.mm"
include "3lt8.mm"
include "2re.mm"
include "3re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt8



  assert |- 2 < 8

  proof
    c2
    c3
    clt
    wbr
    c3
    c8
    clt
    wbr
    c2
    c8
    clt
    wbr
    2lt3
    3lt8
    c2
    c3
    c8
    2re
    3re
    8re
    lttri
    mp2an
end
