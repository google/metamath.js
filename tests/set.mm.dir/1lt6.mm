include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "1lt2.mm"
include "2lt6.mm"
include "1re.mm"
include "2re.mm"
include "6re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt6



  assert |- 1 < 6

  proof
    c1
    c2
    clt
    wbr
    c2
    c6
    clt
    wbr
    c1
    c6
    clt
    wbr
    1lt2
    2lt6
    c1
    c2
    c6
    1re
    2re
    6re
    lttri
    mp2an
end
