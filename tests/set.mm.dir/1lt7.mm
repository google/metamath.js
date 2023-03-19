include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c7.mm"
include "1lt2.mm"
include "2lt7.mm"
include "1re.mm"
include "2re.mm"
include "7re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt7



  assert |- 1 < 7

  proof
    c1
    c2
    clt
    wbr
    c2
    c7
    clt
    wbr
    c1
    c7
    clt
    wbr
    1lt2
    2lt7
    c1
    c2
    c7
    1re
    2re
    7re
    lttri
    mp2an
end
