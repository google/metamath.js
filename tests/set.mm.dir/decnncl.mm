include "cdc.mm"
include "c1.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn.mm"
include "dfdec10.mm"
include "10nn0.mm"
include "numnncl.mm"
include "eqeltri.mm"

theorem decnncl
  let cA: class A
  let cB: class B
  assume decnncl.1: |- A e. NN0
  assume decnncl.2: |- B e. NN


  assert |- ; A B e. NN

  proof
    cA
    cB
    cdc
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    cB
    caddc
    co
    cn
    cA
    cB
    dfdec10
    cA
    cB
    @0
    10nn0
    decnncl.1
    decnncl.2
    numnncl
    eqeltri
end
