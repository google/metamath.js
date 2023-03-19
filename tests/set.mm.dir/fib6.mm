include "c5.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "c6.mm"
include "c8.mm"
include "5p1e6.mm"
include "fveq2i.mm"
include "cmin.mm"
include "c3.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "5nn.mm"
include "fibp1.mm"
include "ax-mp.mm"
include "c4.mm"
include "5cn.mm"
include "ax-1cn.mm"
include "4cn.mm"
include "4p1e5.mm"
include "addcomli.mm"
include "subaddrii.mm"
include "fib4.mm"
include "eqtri.mm"
include "fib5.mm"
include "oveq12i.mm"
include "3cn.mm"
include "5p3e8.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem fib6



  assert |- ( Fibci ` 6 ) = 8

  proof
    c5
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    c6
    cfib
    cfv
    c8
    @0
    c6
    cfib
    5p1e6
    fveq2i
    @1
    c5
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    c5
    cfib
    cfv
    #
    caddc
    co
    #
    c3
    c5
    caddc
    co
    c8
    c5
    cn
    wcel
    @1
    @5
    wceq
    5nn
    c5
    fibp1
    ax-mp
    @3
    c3
    @4
    c5
    caddc
    @3
    c4
    cfib
    cfv
    c3
    @2
    c4
    cfib
    c5
    c1
    c4
    5cn
    ax-1cn
    4cn
    c4
    c1
    c5
    4cn
    ax-1cn
    4p1e5
    addcomli
    subaddrii
    fveq2i
    fib4
    eqtri
    fib5
    oveq12i
    c5
    c3
    c8
    5cn
    3cn
    5p3e8
    addcomli
    3eqtri
    eqtr3i
end
