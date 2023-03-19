include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "10nn0.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "numsuc.mm"
include "eqtr4i.mm"

theorem decsuc
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  assume declt.a: |- A e. NN0
  assume declt.b: |- B e. NN0
  assume decsuc.c: |- ( B + 1 ) = C
  assume decsuc.n: |- N = ; A B


  assert |- ( N + 1 ) = ; A C

  proof
    cN
    c1
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
    cC
    caddc
    co
    cA
    cC
    cdc
    cA
    cB
    cC
    @0
    cN
    10nn0
    declt.a
    declt.b
    decsuc.c
    cN
    cA
    cB
    cdc
    @1
    cB
    caddc
    co
    decsuc.n
    cA
    cB
    dfdec10
    eqtri
    numsuc
    cA
    cC
    dfdec10
    eqtr4i
end
