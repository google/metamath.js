include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cdc.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "1nn0.mm"
include "eqcomi.mm"
include "decsuc.mm"
include "3eqtr2i.mm"

theorem 6p5lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume 6p5lem.1: |- A e. NN0
  assume 6p5lem.2: |- D e. NN0
  assume 6p5lem.3: |- E e. NN0
  assume 6p5lem.4: |- B = ( D + 1 )
  assume 6p5lem.5: |- C = ( E + 1 )
  assume 6p5lem.6: |- ( A + D ) = ; 1 E


  assert |- ( A + B ) = ; 1 C

  proof
    cA
    cB
    caddc
    co
    cA
    cD
    c1
    caddc
    co
    #
    caddc
    co
    cA
    cD
    caddc
    co
    #
    c1
    caddc
    co
    c1
    cC
    cdc
    cB
    @0
    cA
    caddc
    6p5lem.4
    oveq2i
    cA
    cD
    c1
    cA
    6p5lem.1
    nn0cni
    cD
    6p5lem.2
    nn0cni
    ax-1cn
    addassi
    c1
    cE
    cC
    @1
    1nn0
    6p5lem.3
    cC
    cE
    c1
    caddc
    co
    6p5lem.5
    eqcomi
    6p5lem.6
    decsuc
    3eqtr2i
end
