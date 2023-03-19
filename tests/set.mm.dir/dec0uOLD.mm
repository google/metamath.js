include "c10.mm"
include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "num0u.mm"
include "dfdecOLD.mm"
include "eqtr4i.mm"

theorem dec0uOLD
  let cA: class A
  assume dec0u.1: |- A e. NN0


  assert |- ( 10 x. A ) = ; A 0

  proof
    c10
    cA
    cmul
    co
    #
    @0
    cc0
    caddc
    co
    cA
    cc0
    cdc
    cA
    c10
    10nn0OLD
    dec0u.1
    num0u
    cA
    cc0
    dfdecOLD
    eqtr4i
end
