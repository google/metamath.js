include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c10.mm"
include "cmul.mm"
include "cc0.mm"
include "cdc.mm"
include "c9.mm"
include "9nn0.mm"
include "df-10OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "numsucc.mm"
include "eqtr4i.mm"

theorem decsuccOLD
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
    c10
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
    c10
    cN
    c9
    9nn0
    df-10OLD
    decsucc.1
    decsucc.2
    cN
    cA
    c9
    cdc
    c10
    cA
    cmul
    co
    c9
    caddc
    co
    decsucc.3
    cA
    c9
    dfdecOLD
    eqtri
    numsucc
    cB
    cc0
    dfdecOLD
    eqtr4i
end
