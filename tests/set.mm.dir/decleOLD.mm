include "c10.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cdc.mm"
include "cle.mm"
include "wbr.mm"
include "nn0rei.mm"
include "10reOLD.mm"
include "remulcli.mm"
include "leadd2i.mm"
include "mpbi.mm"
include "dfdecOLD.mm"
include "3brtr4i.mm"

theorem decleOLD
  let cA: class A
  let cB: class B
  let cC: class C
  assume decleOLD.1: |- A e. NN0
  assume decleOLD.2: |- B e. NN0
  assume decleOLD.3: |- C e. NN0
  assume decleOLD.4: |- B <_ C


  assert |- ; A B <_ ; A C

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
    @0
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
    @1
    @2
    cle
    wbr
    decleOLD.4
    cB
    cC
    @0
    cB
    decleOLD.2
    nn0rei
    cC
    decleOLD.3
    nn0rei
    c10
    cA
    10reOLD
    cA
    decleOLD.1
    nn0rei
    remulcli
    leadd2i
    mpbi
    cA
    cB
    dfdecOLD
    cA
    cC
    dfdecOLD
    3brtr4i
end
