include "cc0.mm"
include "c2.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "caddc.mm"
include "cpr.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "2z.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "2m1e1.mm"
include "0p1e1.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "0z.mm"
include "fzpr.mm"
include "preq2i.mm"
include "syl6eq.mm"
include "3eqtri.mm"

theorem fzo0to2pr



  assert |- ( 0 ..^ 2 ) = { 0 , 1 }

  proof
    cc0
    c2
    cfzo
    co
    #
    cc0
    c2
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    cc0
    c1
    caddc
    co
    #
    cfz
    co
    #
    cc0
    c1
    cpr
    #
    c2
    cz
    wcel
    @0
    @2
    wceq
    2z
    cc0
    c2
    fzoval
    ax-mp
    @1
    @3
    cc0
    cfz
    @1
    c1
    @3
    2m1e1
    0p1e1
    eqtr4i
    oveq2i
    cc0
    cz
    wcel
    #
    @4
    @5
    wceq
    0z
    @6
    @4
    cc0
    @3
    cpr
    @5
    cc0
    fzpr
    @3
    c1
    cc0
    0p1e1
    preq2i
    syl6eq
    ax-mp
    3eqtri
end
