include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0cni.mm"
include "mul01i.mm"
include "oveq1i.mm"
include "addid2i.mm"
include "eqtr2i.mm"

theorem num0h
  let cA: class A
  let cT: class T
  assume numnncl.1: |- T e. NN0
  assume numnncl.2: |- A e. NN0


  assert |- A = ( ( T x. 0 ) + A )

  proof
    cT
    cc0
    cmul
    co
    #
    cA
    caddc
    co
    cc0
    cA
    caddc
    co
    cA
    @0
    cc0
    cA
    caddc
    cT
    cT
    numnncl.1
    nn0cni
    mul01i
    oveq1i
    cA
    cA
    numnncl.2
    nn0cni
    addid2i
    eqtr2i
end
