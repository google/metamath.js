include "c5.mm"
include "cdc.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "5nn.mm"
include "2nn0.mm"
include "nn0mulcli.mm"
include "caddc.mm"
include "c1.mm"
include "cc0.mm"
include "5cn.mm"
include "2cn.mm"
include "nn0cni.mm"
include "mulassi.mm"
include "5t2e10.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "dfdec10.mm"
include "eqtr4i.mm"
include "ndvdsi.mm"

theorem dec5dvds
  let cA: class A
  let cB: class B
  assume dec5dvds.1: |- A e. NN0
  assume dec5dvds.2: |- B e. NN
  assume dec5dvds.3: |- B < 5


  assert |- -. 5 || ; A B

  proof
    c5
    cA
    cB
    cdc
    #
    c2
    cA
    cmul
    co
    #
    cB
    5nn
    c2
    cA
    2nn0
    dec5dvds.1
    nn0mulcli
    dec5dvds.2
    c5
    @1
    cmul
    co
    #
    cB
    caddc
    co
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
    @0
    @2
    @4
    cB
    caddc
    c5
    c2
    cmul
    co
    #
    cA
    cmul
    co
    @2
    @4
    c5
    c2
    cA
    5cn
    2cn
    cA
    dec5dvds.1
    nn0cni
    mulassi
    @5
    @3
    cA
    cmul
    5t2e10
    oveq1i
    eqtr3i
    oveq1i
    cA
    cB
    dfdec10
    eqtr4i
    dec5dvds.3
    ndvdsi
end
