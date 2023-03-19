include "cc0.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "df-neg.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "0cn.mm"
include "subid.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem neg0



  assert |- -u 0 = 0

  proof
    cc0
    cneg
    cc0
    cc0
    cmin
    co
    #
    cc0
    cc0
    df-neg
    cc0
    cc
    wcel
    @0
    cc0
    wceq
    0cn
    cc0
    subid
    ax-mp
    eqtri
end
