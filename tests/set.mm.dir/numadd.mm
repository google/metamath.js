include "c1.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn0.mm"
include "numcl.mm"
include "eqeltri.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "oveq1i.mm"
include "1nn0.mm"
include "eqtri.mm"
include "numma.mm"
include "eqtr3i.mm"

theorem numadd
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  assume numma.1: |- T e. NN0
  assume numma.2: |- A e. NN0
  assume numma.3: |- B e. NN0
  assume numma.4: |- C e. NN0
  assume numma.5: |- D e. NN0
  assume numma.6: |- M = ( ( T x. A ) + B )
  assume numma.7: |- N = ( ( T x. C ) + D )
  assume numadd.8: |- ( A + C ) = E
  assume numadd.9: |- ( B + D ) = F


  assert |- ( M + N ) = ( ( T x. E ) + F )

  proof
    cM
    c1
    cmul
    co
    #
    cN
    caddc
    co
    cM
    cN
    caddc
    co
    cT
    cE
    cmul
    co
    cF
    caddc
    co
    @0
    cM
    cN
    caddc
    cM
    cM
    cM
    cT
    cA
    cmul
    co
    cB
    caddc
    co
    cn0
    numma.6
    cA
    cB
    cT
    numma.1
    numma.2
    numma.3
    numcl
    eqeltri
    nn0cni
    mulid1i
    oveq1i
    cA
    cB
    cC
    cD
    c1
    cT
    cE
    cF
    cM
    cN
    numma.1
    numma.2
    numma.3
    numma.4
    numma.5
    numma.6
    numma.7
    1nn0
    cA
    c1
    cmul
    co
    #
    cC
    caddc
    co
    cA
    cC
    caddc
    co
    cE
    @1
    cA
    cC
    caddc
    cA
    cA
    numma.2
    nn0cni
    mulid1i
    oveq1i
    numadd.8
    eqtri
    cB
    c1
    cmul
    co
    #
    cD
    caddc
    co
    cB
    cD
    caddc
    co
    cF
    @2
    cB
    cD
    caddc
    cB
    cB
    numma.3
    nn0cni
    mulid1i
    oveq1i
    numadd.9
    eqtri
    numma
    eqtr3i
end
