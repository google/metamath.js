include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn0.mm"
include "dfdecOLD.mm"
include "10nn0OLD.mm"
include "numcl.mm"
include "eqeltri.mm"

theorem decclOLD
  let cA: class A
  let cB: class B
  assume deccl.1: |- A e. NN0
  assume deccl.2: |- B e. NN0


  assert |- ; A B e. NN0

  proof
    cA
    cB
    cdc
    c10
    cA
    cmul
    co
    cB
    caddc
    co
    cn0
    cA
    cB
    dfdecOLD
    cA
    cB
    c10
    10nn0OLD
    deccl.1
    deccl.2
    numcl
    eqeltri
end
