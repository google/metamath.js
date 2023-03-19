include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "oveq1i.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "ax-1cn.mm"
include "addassi.mm"
include "oveq2i.mm"
include "3eqtri.mm"

theorem numsuc
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let cN: class N
  assume numnncl.1: |- T e. NN0
  assume numnncl.2: |- A e. NN0
  assume numcl.2: |- B e. NN0
  assume numsuc.4: |- ( B + 1 ) = C
  assume numsuc.5: |- N = ( ( T x. A ) + B )


  assert |- ( N + 1 ) = ( ( T x. A ) + C )

  proof
    cN
    c1
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
    c1
    caddc
    co
    @0
    cB
    c1
    caddc
    co
    #
    caddc
    co
    @0
    cC
    caddc
    co
    cN
    @1
    c1
    caddc
    numsuc.5
    oveq1i
    @0
    cB
    c1
    @0
    cT
    cA
    numnncl.1
    numnncl.2
    nn0mulcli
    nn0cni
    cB
    numcl.2
    nn0cni
    ax-1cn
    addassi
    @2
    cC
    @0
    caddc
    numsuc.4
    oveq2i
    3eqtri
end
