include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c10.mm"
include "cmul.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "numsuc.mm"
include "eqtr4i.mm"

theorem decsucOLD
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
    c10
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
    c10
    cN
    10nn0OLD
    declt.a
    declt.b
    decsuc.c
    cN
    cA
    cB
    cdc
    @0
    cB
    caddc
    co
    decsuc.n
    cA
    cB
    dfdecOLD
    eqtri
    numsuc
    cA
    cC
    dfdecOLD
    eqtr4i
end
