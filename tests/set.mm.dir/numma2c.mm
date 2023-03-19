include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0cni.mm"
include "cn0.mm"
include "numcl.mm"
include "eqeltri.mm"
include "mulcomi.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "nummac.mm"

theorem numma2c
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  assume numma.1: |- T e. NN0
  assume numma.2: |- A e. NN0
  assume numma.3: |- B e. NN0
  assume numma.4: |- C e. NN0
  assume numma.5: |- D e. NN0
  assume numma.6: |- M = ( ( T x. A ) + B )
  assume numma.7: |- N = ( ( T x. C ) + D )
  assume numma2c.8: |- P e. NN0
  assume numma2c.9: |- F e. NN0
  assume numma2c.10: |- G e. NN0
  assume numma2c.11: |- ( ( P x. A ) + ( C + G ) ) = E
  assume numma2c.12: |- ( ( P x. B ) + D ) = ( ( T x. G ) + F )


  assert |- ( ( P x. M ) + N ) = ( ( T x. E ) + F )

  proof
    cP
    cM
    cmul
    co
    #
    cN
    caddc
    co
    cM
    cP
    cmul
    co
    #
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
    @1
    cN
    caddc
    cP
    cM
    cP
    numma2c.8
    nn0cni
    #
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
    mulcomi
    oveq1i
    cA
    cB
    cC
    cD
    cP
    cT
    cE
    cF
    cG
    cM
    cN
    numma.1
    numma.2
    numma.3
    numma.4
    numma.5
    numma.6
    numma.7
    numma2c.8
    numma2c.9
    numma2c.10
    cA
    cP
    cmul
    co
    #
    cC
    cG
    caddc
    co
    #
    caddc
    co
    cP
    cA
    cmul
    co
    #
    @4
    caddc
    co
    cE
    @3
    @5
    @4
    caddc
    cA
    cP
    cA
    numma.2
    nn0cni
    @2
    mulcomi
    oveq1i
    numma2c.11
    eqtri
    cB
    cP
    cmul
    co
    #
    cD
    caddc
    co
    cP
    cB
    cmul
    co
    #
    cD
    caddc
    co
    cT
    cG
    cmul
    co
    cF
    caddc
    co
    @6
    @7
    cD
    caddc
    cB
    cP
    cB
    numma.3
    nn0cni
    @2
    mulcomi
    oveq1i
    numma2c.12
    eqtri
    nummac
    eqtri
end
