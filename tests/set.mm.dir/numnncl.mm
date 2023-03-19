include "cmul.mm"
include "co.mm"
include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "caddc.mm"
include "nn0mulcli.mm"
include "nn0nnaddcl.mm"
include "mp2an.mm"

theorem numnncl
  let cA: class A
  let cB: class B
  let cT: class T
  assume numnncl.1: |- T e. NN0
  assume numnncl.2: |- A e. NN0
  assume numnncl.3: |- B e. NN


  assert |- ( ( T x. A ) + B ) e. NN

  proof
    cT
    cA
    cmul
    co
    #
    cn0
    wcel
    cB
    cn
    wcel
    @0
    cB
    caddc
    co
    cn
    wcel
    cT
    cA
    numnncl.1
    numnncl.2
    nn0mulcli
    numnncl.3
    @0
    cB
    nn0nnaddcl
    mp2an
end
