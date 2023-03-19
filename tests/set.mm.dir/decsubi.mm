include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "10nn0.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addsubassi.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "3eqtr4i.mm"

theorem decsubi
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
    c1
    cc0
    cdc
    #
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
    @1
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
    @1
    cB
    cN
    @1
    @0
    cA
    10nn0
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
    @2
    cN
    cmin
    cM
    cA
    cB
    cdc
    @2
    decaddi.4
    cA
    cB
    dfdec10
    eqtri
    oveq1i
    @5
    @1
    cC
    caddc
    co
    @4
    cA
    cC
    dfdec10
    cC
    @3
    @1
    caddc
    @3
    cC
    decsubi.5
    eqcomi
    oveq2i
    eqtri
    3eqtr4i
end
