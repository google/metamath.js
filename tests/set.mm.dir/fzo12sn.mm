include "c1.mm"
include "c2.mm"
include "cfzo.mm"
include "co.mm"
include "caddc.mm"
include "csn.mm"
include "df-2.mm"
include "oveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "1z.mm"
include "fzosn.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem fzo12sn



  assert |- ( 1 ..^ 2 ) = { 1 }

  proof
    c1
    c2
    cfzo
    co
    c1
    c1
    c1
    caddc
    co
    #
    cfzo
    co
    #
    c1
    csn
    #
    c2
    @0
    c1
    cfzo
    df-2
    oveq2i
    c1
    cz
    wcel
    @1
    @2
    wceq
    1z
    c1
    fzosn
    ax-mp
    eqtri
end
