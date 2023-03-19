include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "1lt2.mm"
include "2lt8.mm"
include "1re.mm"
include "2re.mm"
include "8re.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt8



  assert |- 1 < 8

  proof
    c1
    c2
    clt
    wbr
    c2
    c8
    clt
    wbr
    c1
    c8
    clt
    wbr
    1lt2
    2lt8
    c1
    c2
    c8
    1re
    2re
    8re
    lttri
    mp2an
end
