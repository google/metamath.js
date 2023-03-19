include "c1.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "caddc.mm"
include "cpr.mm"
include "c2.mm"
include "cmin.mm"
include "cfz.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "3z.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "3m1e2.mm"
include "1p1e2.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "1z.mm"
include "fzpr.mm"
include "3eqtri.mm"
include "preq2i.mm"
include "eqtri.mm"

theorem fzo13pr



  assert |- ( 1 ..^ 3 ) = { 1 , 2 }

  proof
    c1
    c3
    cfzo
    co
    #
    c1
    c1
    c1
    caddc
    co
    #
    cpr
    #
    c1
    c2
    cpr
    @0
    c1
    c3
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    @1
    cfz
    co
    #
    @2
    c3
    cz
    wcel
    @0
    @4
    wceq
    3z
    c1
    c3
    fzoval
    ax-mp
    @3
    @1
    c1
    cfz
    @3
    c2
    @1
    3m1e2
    1p1e2
    eqtr4i
    oveq2i
    c1
    cz
    wcel
    @5
    @2
    wceq
    1z
    c1
    fzpr
    ax-mp
    3eqtri
    @1
    c2
    c1
    1p1e2
    preq2i
    eqtri
end
