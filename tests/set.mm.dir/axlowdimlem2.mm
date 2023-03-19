include "c2.mm"
include "c3.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "2lt3.mm"
include "fzdisj.mm"
include "ax-mp.mm"

theorem axlowdimlem2
  let cN: class N


  assert |- ( ( 1 ... 2 ) i^i ( 3 ... N ) ) = (/)

  proof
    c2
    c3
    clt
    wbr
    c1
    c2
    cfz
    co
    c3
    cN
    cfz
    co
    cin
    c0
    wceq
    2lt3
    c1
    c2
    c3
    cN
    fzdisj
    ax-mp
end
