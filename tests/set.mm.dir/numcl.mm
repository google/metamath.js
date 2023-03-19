include "cmul.mm"
include "co.mm"
include "nn0mulcli.mm"
include "nn0addcli.mm"

theorem numcl
  let cA: class A
  let cB: class B
  let cT: class T
  assume numnncl.1: |- T e. NN0
  assume numnncl.2: |- A e. NN0
  assume numcl.2: |- B e. NN0


  assert |- ( ( T x. A ) + B ) e. NN0

  proof
    cT
    cA
    cmul
    co
    cB
    cT
    cA
    numnncl.1
    numnncl.2
    nn0mulcli
    numcl.2
    nn0addcli
end
