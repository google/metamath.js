include "c1.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "c10.mm"
include "1lt2.mm"
include "2lt10OLD.mm"
include "1re.mm"
include "2re.mm"
include "10reOLD.mm"
include "lttri.mm"
include "mp2an.mm"

theorem 1lt10OLD



  assert |- 1 < 10

  proof
    c1
    c2
    clt
    wbr
    c2
    c10
    clt
    wbr
    c1
    c10
    clt
    wbr
    1lt2
    2lt10OLD
    c1
    c2
    c10
    1re
    2re
    10reOLD
    lttri
    mp2an
end
