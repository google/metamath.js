include "cc0.mm"
include "0nn0.mm"
include "dec0h.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "decadd.mm"

theorem decaddi
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume decaddi.1: |- A e. NN0
  assume decaddi.2: |- B e. NN0
  assume decaddi.3: |- N e. NN0
  assume decaddi.4: |- M = ; A B
  assume decaddi.5: |- ( B + N ) = C


  assert |- ( M + N ) = ; A C

  proof
    cA
    cB
    cc0
    cN
    cA
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
    cA
    decaddi.1
    nn0cni
    addid1i
    decaddi.5
    decadd
end
