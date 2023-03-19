include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addsubassi.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem decsubiOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cN: class N
  assume decaddi.1: |- A e. NN0
  assume decaddi.2: |- B e. NN0
  assume decaddi.3: |- N e. NN0
  assume decaddi.4: |- M = ; A B
  assume decaddci.5: |- ( A + 1 ) = D
  assume decsubi.5: |- ( B - N ) = C


  assert |- ( M - N ) = ; A C

  proof
    c10
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    cN
    cmin
    co
    @0
    cB
    cN
    cmin
    co
    #
    caddc
    co
    #
    cM
    cN
    cmin
    co
    cA
    cC
    cdc
    #
    @0
    cB
    cN
    @0
    c10
    cA
    10nn0OLD
    decaddi.1
    nn0mulcli
    nn0cni
    cB
    decaddi.2
    nn0cni
    cN
    decaddi.3
    nn0cni
    addsubassi
    cM
    @1
    cN
    cmin
    cM
    cA
    cB
    cdc
    @1
    decaddi.4
    cA
    cB
    dfdecOLD
    eqtri
    oveq1i
    @4
    @0
    cC
    caddc
    co
    @3
    cA
    cC
    dfdecOLD
    cC
    @2
    @0
    caddc
    @2
    cC
    decsubi.5
    eqcomi
    oveq2i
    eqtri
    3eqtr4i
end
