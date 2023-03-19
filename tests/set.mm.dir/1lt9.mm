include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c9.mm"
include "1lt2.mm"
include "2lt9.mm"
include "1re.mm"
include "2re.mm"
include "9re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt9



  assert |- 1 < 9

  proof
    c1
    c2
    clt
    wbr
    c2
    c9
    clt
    wbr
    c1
    c9
    clt
    wbr
    1lt2
    2lt9
    c1
    c2
    c9
    1re
    2re
    9re
    lttri
    mp2an
end
