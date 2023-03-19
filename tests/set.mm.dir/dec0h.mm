include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "10nn0.mm"
include "num0h.mm"
include "dfdec10.mm"
include "eqtr4i.mm"

theorem dec0h
  let cA: class A
  assume dec0u.1: |- A e. NN0


  assert |- A = ; 0 A

  proof
    cA
    c1
    cc0
    cdc
    #
    cc0
    cmul
    co
    cA
    caddc
    co
    cc0
    cA
    cdc
    cA
    @0
    10nn0
    dec0u.1
    num0h
    cc0
    cA
    dfdec10
    eqtr4i
end
