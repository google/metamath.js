include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c4.mm"
include "1lt2.mm"
include "2lt4.mm"
include "1re.mm"
include "2re.mm"
include "4re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt4



  assert |- 1 < 4

  proof
    c1
    c2
    clt
    wbr
    c2
    c4
    clt
    wbr
    c1
    c4
    clt
    wbr
    1lt2
    2lt4
    c1
    c2
    c4
    1re
    2re
    4re
    lttri
    mp2an
end
