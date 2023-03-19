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
include "ax-1cn.mm"
include "addassi.mm"
include "3eqtr2i.mm"
include "eqtri.mm"
include "nummac.mm"
include "eqtr3i.mm"

theorem numaddc
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
  assume numaddc.8: |- F e. NN0
  assume numaddc.9: |- ( ( A + C ) + 1 ) = E
  assume numaddc.10: |- ( B + D ) = ( ( T x. 1 ) + F )


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
    c1
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
    numaddc.8
    1nn0
    cA
    c1
    cmul
    co
    #
    cC
    c1
    caddc
    co
    #
    caddc
    co
    cA
    @2
    caddc
    co
    cA
    cC
    caddc
    co
    c1
    caddc
    co
    cE
    @1
    cA
    @2
    caddc
    cA
    cA
    numma.2
    nn0cni
    #
    mulid1i
    oveq1i
    cA
    cC
    c1
    @3
    cC
    numma.4
    nn0cni
    ax-1cn
    addassi
    numaddc.9
    3eqtr2i
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
    cT
    c1
    cmul
    co
    cF
    caddc
    co
    @4
    cB
    cD
    caddc
    cB
    cB
    numma.3
    nn0cni
    mulid1i
    oveq1i
    numaddc.10
    eqtri
    nummac
    eqtr3i
end
