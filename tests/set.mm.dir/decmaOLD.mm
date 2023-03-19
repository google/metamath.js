include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "numma.mm"
include "eqtr4i.mm"

theorem decmaOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
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
  assume decma.p: |- P e. NN0
  assume decma.e: |- ( ( A x. P ) + C ) = E
  assume decma.f: |- ( ( B x. P ) + D ) = F


  assert |- ( ( M x. P ) + N ) = ; E F

  proof
    cM
    cP
    cmul
    co
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
    cP
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
    decma.p
    decma.e
    decma.f
    numma
    cE
    cF
    dfdecOLD
    eqtr4i
end
