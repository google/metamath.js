include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cmul.mm"
include "10nn0.mm"
include "dfdec10.mm"
include "eqtri.mm"
include "numaddc.mm"
include "eqtr4i.mm"

theorem decaddc
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  assume decma.a: |- A e. NN0
  assume decma.b: |- B e. NN0
  assume decma.c: |- C e. NN0
  assume decma.d: |- D e. NN0
  assume decma.m: |- M = ; A B
  assume decma.n: |- N = ; C D
  assume decaddc.e: |- ( ( A + C ) + 1 ) = E
  assume decaddc.f: |- F e. NN0
  assume decaddc.2: |- ( B + D ) = ; 1 F


  assert |- ( M + N ) = ; E F

  proof
    cM
    cN
    caddc
    co
    c1
    cc0
    cdc
    #
    cE
    cmul
    co
    cF
    caddc
    co
    cE
    cF
    cdc
    cA
    cB
    cC
    cD
    @0
    cE
    cF
    cM
    cN
    10nn0
    decma.a
    decma.b
    decma.c
    decma.d
    cM
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
    decma.m
    cA
    cB
    dfdec10
    eqtri
    cN
    cC
    cD
    cdc
    @0
    cC
    cmul
    co
    cD
    caddc
    co
    decma.n
    cC
    cD
    dfdec10
    eqtri
    decaddc.f
    decaddc.e
    cB
    cD
    caddc
    co
    c1
    cF
    cdc
    @0
    c1
    cmul
    co
    cF
    caddc
    co
    decaddc.2
    c1
    cF
    dfdec10
    eqtri
    numaddc
    cE
    cF
    dfdec10
    eqtr4i
end
