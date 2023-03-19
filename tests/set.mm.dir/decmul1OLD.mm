include "cmul.mm"
include "co.mm"
include "c10.mm"
include "caddc.mm"
include "cdc.mm"
include "cc0.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "0nn0.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "addid2i.mm"
include "eqtr4i.mm"
include "mul01i.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "nummul1c.mm"

theorem decmul1OLD
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
    c10
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
    c10
    cc0
    cN
    10nn0OLD
    decmul1.p
    decmul1.a
    decmul1.b
    cN
    cA
    cB
    cdc
    c10
    cA
    cmul
    co
    cB
    caddc
    co
    decmul1.n
    cA
    cB
    dfdecOLD
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
    @0
    cC
    @0
    @0
    cA
    cP
    decmul1.a
    decmul1.p
    nn0mulcli
    nn0cni
    addid1i
    decmul1.c
    eqtri
    cB
    cP
    cmul
    co
    #
    cc0
    cD
    caddc
    co
    #
    c10
    cc0
    cmul
    co
    #
    cD
    caddc
    co
    @1
    cD
    @2
    decmul1.d
    cD
    cD
    decmul1.0
    nn0cni
    addid2i
    eqtr4i
    cc0
    @3
    cD
    caddc
    @3
    cc0
    c10
    c10
    10nn0OLD
    nn0cni
    mul01i
    eqcomi
    oveq1i
    eqtri
    nummul1c
    cC
    cD
    dfdecOLD
    eqtr4i
end
