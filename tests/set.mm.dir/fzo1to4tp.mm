include "c1.mm"
include "c4.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "c2.mm"
include "caddc.mm"
include "c3.mm"
include "ctp.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "4z.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "4m1e3.mm"
include "df-3.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "addcomi.mm"
include "3eqtri.mm"
include "oveq2i.mm"
include "1z.mm"
include "fztp.mm"
include "eqidd.mm"
include "1p1e2.mm"
include "a1i.mm"
include "1p2e3.mm"
include "tpeq123d.mm"
include "eqtrd.mm"

theorem fzo1to4tp



  assert |- ( 1 ..^ 4 ) = { 1 , 2 , 3 }

  proof
    c1
    c4
    cfzo
    co
    #
    c1
    c4
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    c1
    c2
    caddc
    co
    #
    cfz
    co
    #
    c1
    c2
    c3
    ctp
    #
    c4
    cz
    wcel
    @0
    @2
    wceq
    4z
    c1
    c4
    fzoval
    ax-mp
    @1
    @3
    c1
    cfz
    @1
    c3
    c2
    c1
    caddc
    co
    @3
    4m1e3
    df-3
    c2
    c1
    2cn
    ax-1cn
    addcomi
    3eqtri
    oveq2i
    c1
    cz
    wcel
    #
    @4
    @5
    wceq
    1z
    @6
    @4
    c1
    c1
    c1
    caddc
    co
    #
    @3
    ctp
    @5
    c1
    fztp
    @6
    c1
    c1
    @7
    c2
    @3
    c3
    @6
    c1
    eqidd
    @7
    c2
    wceq
    @6
    1p1e2
    a1i
    @3
    c3
    wceq
    @6
    1p2e3
    a1i
    tpeq123d
    eqtrd
    ax-mp
    3eqtri
end
