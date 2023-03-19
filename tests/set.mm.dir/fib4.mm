include "c3.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfib.mm"
include "cfv.mm"
include "c4.mm"
include "3p1e4.mm"
include "fveq2i.mm"
include "cmin.mm"
include "c2.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "3nn.mm"
include "fibp1.mm"
include "ax-mp.mm"
include "3m1e2.mm"
include "fib2.mm"
include "eqtri.mm"
include "fib3.mm"
include "oveq12i.mm"
include "1p2e3.mm"
include "3eqtri.mm"
include "eqtr3i.mm"

theorem fib4



  assert |- ( Fibci ` 4 ) = 3

  proof
    c3
    c1
    caddc
    co
    #
    cfib
    cfv
    #
    c4
    cfib
    cfv
    c3
    @0
    c4
    cfib
    3p1e4
    fveq2i
    @1
    c3
    c1
    cmin
    co
    #
    cfib
    cfv
    #
    c3
    cfib
    cfv
    #
    caddc
    co
    #
    c1
    c2
    caddc
    co
    c3
    c3
    cn
    wcel
    @1
    @5
    wceq
    3nn
    c3
    fibp1
    ax-mp
    @3
    c1
    @4
    c2
    caddc
    @3
    c2
    cfib
    cfv
    c1
    @2
    c2
    cfib
    3m1e2
    fveq2i
    fib2
    eqtri
    fib3
    oveq12i
    1p2e3
    3eqtri
    eqtr3i
end
