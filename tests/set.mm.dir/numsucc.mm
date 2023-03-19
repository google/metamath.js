include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "cc0.mm"
include "cn0.mm"
include "1nn0.mm"
include "nn0addcli.mm"
include "eqeltri.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "oveq2i.mm"
include "ax-1cn.mm"
include "adddii.mm"
include "eqcomi.mm"
include "numsuc.mm"
include "3eqtr4ri.mm"
include "eqeltrri.mm"
include "num0u.mm"
include "3eqtri.mm"

theorem numsucc
  let cA: class A
  let cB: class B
  let cT: class T
  let cN: class N
  let cY: class Y
  assume numsucc.1: |- Y e. NN0
  assume numsucc.2: |- T = ( Y + 1 )
  assume numsucc.3: |- A e. NN0
  assume numsucc.4: |- ( A + 1 ) = B
  assume numsucc.5: |- N = ( ( T x. A ) + Y )


  assert |- ( N + 1 ) = ( ( T x. B ) + 0 )

  proof
    cN
    c1
    caddc
    co
    #
    cT
    cA
    c1
    caddc
    co
    #
    cmul
    co
    #
    cT
    cB
    cmul
    co
    #
    @3
    cc0
    caddc
    co
    cT
    cA
    cmul
    co
    #
    cT
    c1
    cmul
    co
    #
    caddc
    co
    @4
    cT
    caddc
    co
    @2
    @0
    @5
    cT
    @4
    caddc
    cT
    cT
    cT
    cY
    c1
    caddc
    co
    #
    cn0
    numsucc.2
    cY
    c1
    numsucc.1
    1nn0
    nn0addcli
    eqeltri
    #
    nn0cni
    #
    mulid1i
    oveq2i
    cT
    cA
    c1
    @8
    cA
    numsucc.3
    nn0cni
    ax-1cn
    adddii
    cA
    cY
    cT
    cT
    cN
    @7
    numsucc.3
    numsucc.1
    cT
    @6
    numsucc.2
    eqcomi
    numsucc.5
    numsuc
    3eqtr4ri
    @1
    cB
    cT
    cmul
    numsucc.4
    oveq2i
    cB
    cT
    @7
    @1
    cB
    cn0
    numsucc.4
    cA
    c1
    numsucc.3
    1nn0
    nn0addcli
    eqeltrri
    num0u
    3eqtri
end
