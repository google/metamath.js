include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "c10.mm"
include "cdc.mm"
include "10nn0OLD.mm"
include "dfdecOLD.mm"
include "eqtri.mm"
include "numma2c.mm"
include "eqtr4i.mm"

theorem decma2cOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume decma.a: |- A e. NN0
  assume decma.b: |- B e. NN0
  assume decma.c: |- C e. NN0
  assume decma.d: |- D e. NN0
  assume decma.m: |- M = ; A B
  assume decma.n: |- N = ; C D
  assume decma2c.p: |- P e. NN0
  assume decma2c.f: |- F e. NN0
  assume decma2c.g: |- G e. NN0
  assume decma2c.e: |- ( ( P x. A ) + ( C + G ) ) = E
  assume decma2c.2: |- ( ( P x. B ) + D ) = ; G F


  assert |- ( ( P x. M ) + N ) = ; E F

  proof
    cP
    cM
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
    cG
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
    decma2c.p
    decma2c.f
    decma2c.g
    decma2c.e
    cP
    cB
    cmul
    co
    cD
    caddc
    co
    cG
    cF
    cdc
    c10
    cG
    cmul
    co
    cF
    caddc
    co
    decma2c.2
    cG
    cF
    dfdecOLD
    eqtri
    numma2c
    cE
    cF
    dfdecOLD
    eqtr4i
end
