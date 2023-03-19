include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "c9.mm"
include "9nn0.mm"
include "9p1e10.mm"
include "eqcomi.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "numsucc.mm"
include "eqtr4i.mm"

theorem decsucc
  let cA: class A
  let cB: class B
  let cN: class N
  assume decsucc.1: |- A e. NN0
  assume decsucc.2: |- ( A + 1 ) = B
  assume decsucc.3: |- N = ; A 9


  assert |- ( N + 1 ) = ; B 0

  proof
    cN
    c1
    caddc
    co
    c1
    cc0
    cdc
    #
    cB
    cmul
    co
    cc0
    caddc
    co
    cB
    cc0
    cdc
    cA
    cB
    @0
    cN
    c9
    9nn0
    c9
    c1
    caddc
    co
    @0
    9p1e10
    eqcomi
    decsucc.1
    decsucc.2
    cN
    cA
    c9
    cdc
    @0
    cA
    cmul
    co
    c9
    caddc
    co
    decsucc.3
    cA
    c9
    dfdec10
    eqtri
    numsucc
    cB
    cc0
    dfdec10
    eqtr4i
end
