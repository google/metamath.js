include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "c3.mm"
include "2p1e3.mm"
include "fveq2i.mm"
include "cmin.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "2nn.mm"
include "fibp1.mm"
include "ax-mp.mm"
include "2m1e1.mm"
include "fib1.mm"
include "eqtri.mm"
include "fib2.mm"
include "oveq12i.mm"
include "1p1e2.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem fib3



  assert |- ( Fibci ` 3 ) = 2

  proof
    c2
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    c3
    cfib
    cfv
    c2
    @0
    c3
    cfib
    2p1e3
    fveq2i
    @1
    c2
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    c2
    cfib
    cfv
    #
    caddc
    co
    #
    c1
    c1
    caddc
    co
    c2
    c2
    cn
    wcel
    @1
    @5
    wceq
    2nn
    c2
    fibp1
    ax-mp
    @3
    c1
    @4
    c1
    caddc
    @3
    c1
    cfib
    cfv
    c1
    @2
    c1
    cfib
    2m1e1
    fveq2i
    fib1
    eqtri
    fib2
    oveq12i
    1p1e2
    3eqtri
    eqtr3i
end
