include "cc0.mm"
include "c3.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "c2.mm"
include "caddc.mm"
include "ctp.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "3z.mm"
include "fzoval.mm"
include "ax-mp.mm"
include "3m1e2.mm"
include "2cn.mm"
include "addid2i.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "0z.mm"
include "fztp.mm"
include "eqidd.mm"
include "0p1e1.mm"
include "a1i.mm"
include "tpeq123d.mm"
include "eqtrd.mm"
include "3eqtri.mm"

theorem fzo0to3tp



  assert |- ( 0 ..^ 3 ) = { 0 , 1 , 2 }

  proof
    cc0
    c3
    cfzo
    co
    #
    cc0
    c3
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    cc0
    c2
    caddc
    co
    #
    cfz
    co
    #
    cc0
    c1
    c2
    ctp
    #
    c3
    cz
    wcel
    @0
    @2
    wceq
    3z
    cc0
    c3
    fzoval
    ax-mp
    @1
    @3
    cc0
    cfz
    @1
    c2
    @3
    3m1e2
    c2
    2cn
    addid2i
    #
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
    @7
    @4
    cc0
    cc0
    c1
    caddc
    co
    #
    @3
    ctp
    @5
    cc0
    fztp
    @7
    cc0
    cc0
    @8
    c1
    @3
    c2
    @7
    cc0
    eqidd
    @8
    c1
    wceq
    @7
    0p1e1
    a1i
    @3
    c2
    wceq
    @7
    @6
    a1i
    tpeq123d
    eqtrd
    ax-mp
    3eqtri
end
