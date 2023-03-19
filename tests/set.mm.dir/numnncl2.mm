include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "caddc.mm"
include "cn.mm"
include "nnmulcli.mm"
include "nncni.mm"
include "addid1i.mm"
include "eqeltri.mm"

theorem numnncl2
  let cA: class A
  let cT: class T
  assume numnncl2.1: |- T e. NN
  assume numnncl2.2: |- A e. NN


  assert |- ( ( T x. A ) + 0 ) e. NN

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
    cn
    @0
    @0
    cT
    cA
    numnncl2.1
    numnncl2.2
    nnmulcli
    #
    nncni
    addid1i
    @1
    eqeltri
end
