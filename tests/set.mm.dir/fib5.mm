include "c4.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "c5.mm"
include "4p1e5.mm"
include "fveq2i.mm"
include "cmin.mm"
include "c2.mm"
include "c3.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn.mm"
include "fibp1.mm"
include "ax-mp.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "3p1e4.mm"
include "addcomli.mm"
include "subaddrii.mm"
include "fib3.mm"
include "eqtri.mm"
include "fib4.mm"
include "oveq12i.mm"
include "2cn.mm"
include "3p2e5.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem fib5



  assert |- ( Fibci ` 5 ) = 5

  proof
    c4
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    c5
    cfib
    cfv
    c5
    @0
    c5
    cfib
    4p1e5
    fveq2i
    @1
    c4
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    c4
    cfib
    cfv
    #
    caddc
    co
    #
    c2
    c3
    caddc
    co
    c5
    c4
    cn
    wcel
    @1
    @5
    wceq
    4nn
    c4
    fibp1
    ax-mp
    @3
    c2
    @4
    c3
    caddc
    @3
    c3
    cfib
    cfv
    c2
    @2
    c3
    cfib
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    c3
    c1
    c4
    3cn
    ax-1cn
    3p1e4
    addcomli
    subaddrii
    fveq2i
    fib3
    eqtri
    fib4
    oveq12i
    c3
    c2
    c5
    3cn
    2cn
    3p2e5
    addcomli
    3eqtri
    eqtr3i
end
