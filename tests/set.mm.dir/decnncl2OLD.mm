include "cc0.mm"
include "cdc.mm"
include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn.mm"
include "dfdecOLD.mm"
include "10nnOLD.mm"
include "numnncl2.mm"
include "eqeltri.mm"

theorem decnncl2OLD
  let cA: class A
  assume decnncl2.1: |- A e. NN


  assert |- ; A 0 e. NN

  proof
    cA
    cc0
    cdc
    c10
    cA
    cmul
    co
    cc0
    caddc
    co
    cn
    cA
    cc0
    dfdecOLD
    cA
    c10
    10nnOLD
    decnncl2.1
    numnncl2
    eqeltri
end
