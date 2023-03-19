include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "nn0cni.mm"
include "mulcli.mm"
include "adddii.mm"
include "mulassi.mm"
include "eqtr4i.mm"
include "adddiri.mm"
include "add4i.mm"
include "oveq2i.mm"
include "3eqtr2i.mm"

theorem numma
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
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
  assume numma.8: |- P e. NN0
  assume numma.9: |- ( ( A x. P ) + C ) = E
  assume numma.10: |- ( ( B x. P ) + D ) = F


  assert |- ( ( M x. P ) + N ) = ( ( T x. E ) + F )

  proof
    cM
    cP
    cmul
    co
    #
    cN
    caddc
    co
    cT
    cA
    cmul
    co
    #
    cB
    caddc
    co
    #
    cP
    cmul
    co
    #
    cT
    cC
    cmul
    co
    #
    cD
    caddc
    co
    #
    caddc
    co
    #
    cT
    cA
    cP
    cmul
    co
    #
    cC
    caddc
    co
    #
    cmul
    co
    #
    cB
    cP
    cmul
    co
    #
    cD
    caddc
    co
    #
    caddc
    co
    #
    cT
    cE
    cmul
    co
    #
    cF
    caddc
    co
    @0
    @3
    cN
    @5
    caddc
    cM
    @2
    cP
    cmul
    numma.6
    oveq1i
    numma.7
    oveq12i
    @12
    @1
    cP
    cmul
    co
    #
    @4
    caddc
    co
    #
    @11
    caddc
    co
    #
    @6
    @9
    @15
    @11
    caddc
    @9
    cT
    @7
    cmul
    co
    #
    @4
    caddc
    co
    @15
    cT
    @7
    cC
    cT
    numma.1
    nn0cni
    #
    cA
    cP
    cA
    numma.2
    nn0cni
    #
    cP
    numma.8
    nn0cni
    #
    mulcli
    cC
    numma.4
    nn0cni
    #
    adddii
    @14
    @17
    @4
    caddc
    cT
    cA
    cP
    @18
    @19
    @20
    mulassi
    oveq1i
    eqtr4i
    oveq1i
    @6
    @14
    @10
    caddc
    co
    #
    @5
    caddc
    co
    @16
    @3
    @22
    @5
    caddc
    @1
    cB
    cP
    cT
    cA
    @18
    @19
    mulcli
    #
    cB
    numma.3
    nn0cni
    #
    @20
    adddiri
    oveq1i
    @14
    @4
    @10
    cD
    @1
    cP
    @23
    @20
    mulcli
    cT
    cC
    @18
    @21
    mulcli
    cB
    cP
    @24
    @20
    mulcli
    cD
    numma.5
    nn0cni
    add4i
    eqtr4i
    eqtr4i
    @9
    @13
    @11
    cF
    caddc
    @8
    cE
    cT
    cmul
    numma.9
    oveq2i
    numma.10
    oveq12i
    3eqtr2i
end
