include "cc0.mm"
include "0nn0.mm"
include "caddc.mm"
include "co.mm"
include "c10.mm"
include "c1.mm"
include "cdc.mm"
include "dec10OLD.mm"
include "eqtri.mm"
include "decaddci.mm"

theorem decaddci2OLD
  let cA: class A
  let cB: class B
  let cD: class D
  let cM: class M
  let cN: class N
  assume decaddi.1: |- A e. NN0
  assume decaddi.2: |- B e. NN0
  assume decaddi.3: |- N e. NN0
  assume decaddi.4: |- M = ; A B
  assume decaddci.5: |- ( A + 1 ) = D
  assume decaddci2OLD.6: |- ( B + N ) = 10


  assert |- ( M + N ) = ; D 0

  proof
    cA
    cB
    cc0
    cD
    cM
    cN
    decaddi.1
    decaddi.2
    decaddi.3
    decaddi.4
    decaddci.5
    0nn0
    cB
    cN
    caddc
    co
    c10
    c1
    cc0
    cdc
    decaddci2OLD.6
    dec10OLD
    eqtri
    decaddci
end
