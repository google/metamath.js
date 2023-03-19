include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c3.mm"
include "1lt2.mm"
include "2lt3.mm"
include "1re.mm"
include "2re.mm"
include "3re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt3



  assert |- 1 < 3

  proof
    c1
    c2
    clt
    wbr
    c2
    c3
    clt
    wbr
    c1
    c3
    clt
    wbr
    1lt2
    2lt3
    c1
    c2
    c3
    1re
    2re
    3re
    lttri
    mp2an
end
