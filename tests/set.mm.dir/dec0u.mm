include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "10nn0.mm"
include "num0u.mm"
include "dfdec10.mm"
include "eqtr4i.mm"

theorem dec0u
  let cA: class A
  assume dec0u.1: |- A e. NN0


  assert |- ( ; 1 0 x. A ) = ; A 0

  proof
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    #
    @1
    cc0
    caddc
    co
    cA
    cc0
    cdc
    cA
    @0
    10nn0
    dec0u.1
    num0u
    cA
    cc0
    dfdec10
    eqtr4i
end
