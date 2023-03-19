include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addid1i.mm"
include "eqcomi.mm"

theorem num0u
  let cA: class A
  let cT: class T
  assume numnncl.1: |- T e. NN0
  assume numnncl.2: |- A e. NN0


  assert |- ( T x. A ) = ( ( T x. A ) + 0 )

  proof
    cT
    cA
    cmul
    co
    #
    cc0
    caddc
    co
    @0
    @0
    @0
    cT
    cA
    numnncl.1
    numnncl.2
    nn0mulcli
    nn0cni
    addid1i
    eqcomi
end
