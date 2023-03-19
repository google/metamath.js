include "cc0.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "caddc.mm"
include "csn.mm"
include "1e0p1.mm"
include "oveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "0z.mm"
include "fzosn.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem fzo01



  assert |- ( 0 ..^ 1 ) = { 0 }

  proof
    cc0
    c1
    cfzo
    co
    cc0
    cc0
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cc0
    csn
    #
    c1
    @0
    cc0
    cfzo
    1e0p1
    oveq2i
    cc0
    cz
    wcel
    @1
    @2
    wceq
    0z
    cc0
    fzosn
    ax-mp
    eqtri
end
