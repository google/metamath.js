include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "caddc.mm"
include "10nn0.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "0nn0.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "oveq2i.mm"
include "addid2i.mm"
include "mul01i.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "3eqtr3i.mm"
include "nummul1c.mm"
include "eqtr4i.mm"

theorem decmul1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cN: class N
  assume decmul1.p: |- P e. NN0
  assume decmul1.a: |- A e. NN0
  assume decmul1.b: |- B e. NN0
  assume decmul1.n: |- N = ; A B
  assume decmul1.0: |- D e. NN0
  assume decmul1.c: |- ( A x. P ) = C
  assume decmul1.d: |- ( B x. P ) = D


  assert |- ( N x. P ) = ; C D

  proof
    cN
    cP
    cmul
    co
    c1
    cc0
    cdc
    #
    cC
    cmul
    co
    cD
    caddc
    co
    cC
    cD
    cdc
    cA
    cB
    cC
    cD
    cP
    @0
    cc0
    cN
    10nn0
    decmul1.p
    decmul1.a
    decmul1.b
    cN
    cA
    cB
    cdc
    @0
    cA
    cmul
    co
    cB
    caddc
    co
    decmul1.n
    cA
    cB
    dfdec10
    eqtri
    decmul1.0
    0nn0
    cA
    cP
    cmul
    co
    #
    cc0
    caddc
    co
    @1
    cC
    @1
    @1
    cA
    cP
    decmul1.a
    decmul1.p
    nn0mulcli
    nn0cni
    addid1i
    decmul1.c
    eqtri
    cc0
    cB
    cP
    cmul
    co
    #
    caddc
    co
    cc0
    cD
    caddc
    co
    @2
    @0
    cc0
    cmul
    co
    #
    cD
    caddc
    co
    @2
    cD
    cc0
    caddc
    decmul1.d
    oveq2i
    @2
    @2
    cB
    cP
    decmul1.b
    decmul1.p
    nn0mulcli
    nn0cni
    addid2i
    cc0
    @3
    cD
    caddc
    @3
    cc0
    @0
    @0
    10nn0
    nn0cni
    mul01i
    eqcomi
    oveq1i
    3eqtr3i
    nummul1c
    cC
    cD
    dfdec10
    eqtr4i
end
