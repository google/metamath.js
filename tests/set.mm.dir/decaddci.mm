include "cc0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "decaddc.mm"

theorem decaddci
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
  assume decaddci.6: |- C e. NN0
  assume decaddci.7: |- ( B + N ) = ; 1 C


  assert |- ( M + N ) = ; D C

  proof
    cA
    cB
    cc0
    cN
    cD
    cC
    cM
    cN
    decaddi.1
    decaddi.2
    0nn0
    decaddi.3
    decaddi.4
    cN
    decaddi.3
    dec0h
    cA
    cc0
    caddc
    co
    #
    c1
    caddc
    co
    cA
    c1
    caddc
    co
    cD
    @0
    cA
    c1
    caddc
    cA
    cA
    decaddi.1
    nn0cni
    addid1i
    oveq1i
    decaddci.5
    eqtri
    decaddci.6
    decaddci.7
    decaddc
end
