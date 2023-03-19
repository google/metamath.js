include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "nn0rei.mm"
include "nnrei.mm"
include "nnnn0i.mm"
include "nn0mulcli.mm"
include "ltadd2i.mm"
include "mpbi.mm"

theorem numlt
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume numlt.1: |- T e. NN
  assume numlt.2: |- A e. NN0
  assume numlt.3: |- B e. NN0
  assume numlt.4: |- C e. NN
  assume numlt.5: |- B < C


  assert |- ( ( T x. A ) + B ) < ( ( T x. A ) + C )

  proof
    cB
    cC
    clt
    wbr
    cT
    cA
    cmul
    co
    #
    cB
    caddc
    co
    @0
    cC
    caddc
    co
    clt
    wbr
    numlt.5
    cB
    cC
    @0
    cB
    numlt.3
    nn0rei
    cC
    numlt.4
    nnrei
    @0
    cT
    cA
    cT
    numlt.1
    nnnn0i
    numlt.2
    nn0mulcli
    nn0rei
    ltadd2i
    mpbi
end
