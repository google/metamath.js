include "caddc.mm"
include "co.mm"
include "c1.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "eqtr3i.mm"
include "eqtri.mm"

theorem unitadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume unitadd.1: |- ( A + B ) = F
  assume unitadd.2: |- ( C + 1 ) = B
  assume unitadd.3: |- A e. NN0
  assume unitadd.4: |- C e. NN0


  assert |- ( ( A + C ) + 1 ) = F

  proof
    cA
    cC
    caddc
    co
    c1
    caddc
    co
    cA
    cC
    c1
    caddc
    co
    #
    caddc
    co
    #
    cF
    cA
    cC
    c1
    cA
    unitadd.3
    nn0cni
    cC
    unitadd.4
    nn0cni
    ax-1cn
    addassi
    cA
    cB
    caddc
    co
    @1
    cF
    cB
    @0
    cA
    caddc
    @0
    cB
    unitadd.2
    eqcomi
    oveq2i
    unitadd.1
    eqtr3i
    eqtri
end
