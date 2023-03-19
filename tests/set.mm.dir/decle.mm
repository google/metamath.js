include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "nn0rei.mm"
include "10nn0.mm"
include "nn0mulcli.mm"
include "leadd2i.mm"
include "mpbi.mm"
include "dfdec10.mm"
include "3brtr4i.mm"

theorem decle
  let cA: class A
  let cB: class B
  let cC: class C
  assume decle.1: |- A e. NN0
  assume decle.2: |- B e. NN0
  assume decle.3: |- C e. NN0
  assume decle.4: |- B <_ C


  assert |- ; A B <_ ; A C

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
    @1
    cC
    caddc
    co
    #
    cA
    cB
    cdc
    cA
    cC
    cdc
    cle
    cB
    cC
    cle
    wbr
    @2
    @3
    cle
    wbr
    decle.4
    cB
    cC
    @1
    cB
    decle.2
    nn0rei
    cC
    decle.3
    nn0rei
    @1
    @0
    cA
    10nn0
    decle.1
    nn0mulcli
    nn0rei
    leadd2i
    mpbi
    cA
    cB
    dfdec10
    cA
    cC
    dfdec10
    3brtr4i
end
