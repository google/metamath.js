include "c2.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "c5.mm"
include "2lt4.mm"
include "4lt5.mm"
include "2re.mm"
include "4re.mm"
include "5re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 2lt5



  assert |- 2 < 5

  proof
    c2
    c4
    clt
    wbr
    c4
    c5
    clt
    wbr
    c2
    c5
    clt
    wbr
    2lt4
    4lt5
    c2
    c4
    c5
    2re
    4re
    5re
    lttri
    mp2an
end
