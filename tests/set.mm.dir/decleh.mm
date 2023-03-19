include "cdc.mm"
include "deccl.mm"
include "nn0rei.mm"
include "declth.mm"
include "ltleii.mm"

theorem decleh
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume decle.1: |- A e. NN0
  assume decle.2: |- B e. NN0
  assume decle.3: |- C e. NN0
  assume decleh.4: |- D e. NN0
  assume decleh.5: |- C <_ 9
  assume decleh.6: |- A < B


  assert |- ; A C <_ ; B D

  proof
    cA
    cC
    cdc
    #
    cB
    cD
    cdc
    #
    @0
    cA
    cC
    decle.1
    decle.3
    deccl
    nn0rei
    @1
    cB
    cD
    decle.2
    decleh.4
    deccl
    nn0rei
    cA
    cB
    cC
    cD
    decle.1
    decle.2
    decle.3
    decleh.4
    decleh.5
    decleh.6
    declth
    ltleii
end
