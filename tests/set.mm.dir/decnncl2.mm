include "cc0.mm"
include "cdc.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn.mm"
include "dfdec10.mm"
include "10nn.mm"
include "numnncl2.mm"
include "eqeltri.mm"

theorem decnncl2
  let cA: class A
  assume decnncl2.1: |- A e. NN


  assert |- ; A 0 e. NN

  proof
    cA
    cc0
    cdc
    c1
    cc0
    cdc
    #
    cA
    cmul
    co
    cc0
    caddc
    co
    cn
    cA
    cc0
    dfdec10
    cA
    @0
    10nn
    decnncl2.1
    numnncl2
    eqeltri
end
