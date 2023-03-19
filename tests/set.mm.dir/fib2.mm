include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "c2.mm"
include "1p1e2.mm"
include "fveq2i.mm"
include "cmin.mm"
include "cc0.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "1nn.mm"
include "fibp1.mm"
include "ax-mp.mm"
include "1m1e0.mm"
include "fib0.mm"
include "eqtri.mm"
include "fib1.mm"
include "oveq12i.mm"
include "0p1e1.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem fib2



  assert |- ( Fibci ` 2 ) = 1

  proof
    c1
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    c2
    cfib
    cfv
    c1
    @0
    c2
    cfib
    1p1e2
    fveq2i
    @1
    c1
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    c1
    cfib
    cfv
    #
    caddc
    co
    #
    cc0
    c1
    caddc
    co
    c1
    c1
    cn
    wcel
    @1
    @5
    wceq
    1nn
    c1
    fibp1
    ax-mp
    @3
    cc0
    @4
    c1
    caddc
    @3
    cc0
    cfib
    cfv
    cc0
    @2
    cc0
    cfib
    1m1e0
    fveq2i
    fib0
    eqtri
    fib1
    oveq12i
    0p1e1
    3eqtri
    eqtr3i
end
