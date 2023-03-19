include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2i.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "adddii.mm"
include "mulid1i.mm"
include "oveq12i.mm"
include "eqtri.mm"

theorem 4t3lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume 4t3lem.1: |- A e. NN0
  assume 4t3lem.2: |- B e. NN0
  assume 4t3lem.3: |- C = ( B + 1 )
  assume 4t3lem.4: |- ( A x. B ) = D
  assume 4t3lem.5: |- ( D + A ) = E


  assert |- ( A x. C ) = E

  proof
    cA
    cC
    cmul
    co
    cA
    cB
    c1
    caddc
    co
    #
    cmul
    co
    #
    cE
    cC
    @0
    cA
    cmul
    4t3lem.3
    oveq2i
    @1
    cD
    cA
    caddc
    co
    #
    cE
    @1
    cA
    cB
    cmul
    co
    #
    cA
    c1
    cmul
    co
    #
    caddc
    co
    @2
    cA
    cB
    c1
    cA
    4t3lem.1
    nn0cni
    #
    cB
    4t3lem.2
    nn0cni
    ax-1cn
    adddii
    @3
    cD
    @4
    cA
    caddc
    4t3lem.4
    cA
    @5
    mulid1i
    oveq12i
    eqtri
    4t3lem.5
    eqtri
    eqtri
end
