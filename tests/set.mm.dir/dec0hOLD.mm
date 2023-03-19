include "c10.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "num0h.mm"
include "dfdecOLD.mm"
include "eqtr4i.mm"

theorem dec0hOLD
  let cA: class A
  assume dec0u.1: |- A e. NN0


  assert |- A = ; 0 A

  proof
    cA
    c10
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
    c10
    10nn0OLD
    dec0u.1
    num0h
    cc0
    cA
    dfdecOLD
    eqtr4i
end
