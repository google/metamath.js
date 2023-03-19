include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn.mm"
include "dfdecOLD.mm"
include "10nn0OLD.mm"
include "numnncl.mm"
include "eqeltri.mm"

theorem decnnclOLD
  let cA: class A
  let cB: class B
  assume decnncl.1: |- A e. NN0
  assume decnncl.2: |- B e. NN


  assert |- ; A B e. NN

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
    cn
    cA
    cB
    dfdecOLD
    cA
    cB
    c10
    10nn0OLD
    decnncl.1
    decnncl.2
    numnncl
    eqeltri
end
