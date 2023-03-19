include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cn0.mm"
include "numcl.mm"
include "eqeltri.mm"
include "nn0cni.mm"
include "mulcomi.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "mulcomli.mm"
include "nummul1c.mm"

theorem nummul2c
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cT: class T
  let cE: class E
  let cN: class N
  assume nummul1c.1: |- T e. NN0
  assume nummul1c.2: |- P e. NN0
  assume nummul1c.3: |- A e. NN0
  assume nummul1c.4: |- B e. NN0
  assume nummul1c.5: |- N = ( ( T x. A ) + B )
  assume nummul1c.6: |- D e. NN0
  assume nummul1c.7: |- E e. NN0
  assume nummul2c.7: |- ( ( P x. A ) + E ) = C
  assume nummul2c.8: |- ( P x. B ) = ( ( T x. E ) + D )


  assert |- ( P x. N ) = ( ( T x. C ) + D )

  proof
    cN
    cP
    cT
    cC
    cmul
    co
    cD
    caddc
    co
    cN
    cN
    cT
    cA
    cmul
    co
    cB
    caddc
    co
    cn0
    nummul1c.5
    cA
    cB
    cT
    nummul1c.1
    nummul1c.3
    nummul1c.4
    numcl
    eqeltri
    nn0cni
    cP
    nummul1c.2
    nn0cni
    #
    cA
    cB
    cC
    cD
    cP
    cT
    cE
    cN
    nummul1c.1
    nummul1c.2
    nummul1c.3
    nummul1c.4
    nummul1c.5
    nummul1c.6
    nummul1c.7
    cA
    cP
    cmul
    co
    #
    cE
    caddc
    co
    cP
    cA
    cmul
    co
    #
    cE
    caddc
    co
    cC
    @1
    @2
    cE
    caddc
    cA
    cP
    cA
    nummul1c.3
    nn0cni
    @0
    mulcomi
    oveq1i
    nummul2c.7
    eqtri
    cP
    cB
    cT
    cE
    cmul
    co
    cD
    caddc
    co
    @0
    cB
    nummul1c.4
    nn0cni
    nummul2c.8
    mulcomli
    nummul1c
    mulcomli
end
