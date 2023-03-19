include "caddc.mm"
include "co.mm"
include "c10.mm"
include "cmul.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "c1.mm"
include "numaddc.mm"
include "eqtr4i.mm"

theorem decaddcOLD
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
    c10
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
    c10
    cE
    cF
    cM
    cN
    10nn0OLD
    decma.a
    decma.b
    decma.c
    decma.d
    cM
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
    decma.m
    cA
    cB
    dfdecOLD
    eqtri
    cN
    cC
    cD
    cdc
    c10
    cC
    cmul
    co
    cD
    caddc
    co
    decma.n
    cC
    cD
    dfdecOLD
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
    c10
    c1
    cmul
    co
    cF
    caddc
    co
    decaddc.2
    c1
    cF
    dfdecOLD
    eqtri
    numaddc
    cE
    cF
    dfdecOLD
    eqtr4i
end
