include "cdc.mm"
include "c1.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cdp.mm"
include "deccl.mm"
include "nn0cni.mm"
include "10nn.mm"
include "nncni.mm"
include "nnne0i.mm"
include "divdiri.mm"
include "oveq1i.mm"
include "eqtr3i.mm"
include "nn0rei.mm"
include "decdiv10.mm"
include "oveq12i.mm"
include "3eqtr3i.mm"

theorem dpadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume dpmul.a: |- A e. NN0
  assume dpmul.b: |- B e. NN0
  assume dpmul.c: |- C e. NN0
  assume dpmul.d: |- D e. NN0
  assume dpmul.e: |- E e. NN0
  assume dpadd.f: |- F e. NN0
  assume dpadd.1: |- ( ; A B + ; C D ) = ; E F


  assert |- ( ( A . B ) + ( C . D ) ) = ( E . F )

  proof
    cA
    cB
    cdc
    #
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    cC
    cD
    cdc
    #
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cE
    cF
    cdc
    #
    @1
    cdiv
    co
    #
    cA
    cB
    cdp
    co
    #
    cC
    cD
    cdp
    co
    #
    caddc
    co
    cE
    cF
    cdp
    co
    @0
    @3
    caddc
    co
    #
    @1
    cdiv
    co
    @5
    @7
    @0
    @3
    @1
    @0
    cA
    cB
    dpmul.a
    dpmul.b
    deccl
    nn0cni
    @3
    cC
    cD
    dpmul.c
    dpmul.d
    deccl
    nn0cni
    @1
    10nn
    nncni
    @1
    10nn
    nnne0i
    divdiri
    @10
    @6
    @1
    cdiv
    dpadd.1
    oveq1i
    eqtr3i
    @2
    @8
    @4
    @9
    caddc
    cA
    cB
    dpmul.a
    cB
    dpmul.b
    nn0rei
    decdiv10
    cC
    cD
    dpmul.c
    cD
    dpmul.d
    nn0rei
    decdiv10
    oveq12i
    cE
    cF
    dpmul.e
    cF
    dpadd.f
    nn0rei
    decdiv10
    3eqtr3i
end
