include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "cn0.mm"
include "numcl.mm"
include "eqeltri.mm"
include "num0u.mm"
include "0nn0.mm"
include "num0h.mm"
include "nn0cni.mm"
include "addid2i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqtr3i.mm"
include "nummac.mm"

theorem nummul1c
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
  assume nummul1c.8: |- ( ( A x. P ) + E ) = C
  assume nummul1c.9: |- ( B x. P ) = ( ( T x. E ) + D )


  assert |- ( N x. P ) = ( ( T x. C ) + D )

  proof
    cN
    cP
    cmul
    co
    #
    @0
    cc0
    caddc
    co
    cT
    cC
    cmul
    co
    cD
    caddc
    co
    cP
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
    nummul1c.2
    num0u
    cA
    cB
    cc0
    cc0
    cP
    cT
    cC
    cD
    cE
    cN
    cc0
    nummul1c.1
    nummul1c.3
    nummul1c.4
    0nn0
    0nn0
    nummul1c.5
    cc0
    cT
    nummul1c.1
    0nn0
    num0h
    nummul1c.2
    nummul1c.6
    nummul1c.7
    cA
    cP
    cmul
    co
    #
    cc0
    cE
    caddc
    co
    #
    caddc
    co
    @1
    cE
    caddc
    co
    cC
    @2
    cE
    @1
    caddc
    cE
    cE
    nummul1c.7
    nn0cni
    addid2i
    oveq2i
    nummul1c.8
    eqtri
    cB
    cP
    cmul
    co
    #
    @3
    cc0
    caddc
    co
    cT
    cE
    cmul
    co
    cD
    caddc
    co
    cP
    cB
    nummul1c.4
    nummul1c.2
    num0u
    nummul1c.9
    eqtr3i
    nummac
    eqtri
end
