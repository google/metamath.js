include "c1.mm"
include "cdc.mm"
include "cmul.mm"
include "co.mm"
include "1nn0.mm"
include "decmulnc.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "deceq12i.mm"
include "eqtri.mm"

theorem 11multnc
  let cN: class N
  assume 11multnc.n: |- N e. NN0


  assert |- ( N x. ; 1 1 ) = ; N N

  proof
    cN
    c1
    c1
    cdc
    cmul
    co
    cN
    c1
    cmul
    co
    #
    @0
    cdc
    cN
    cN
    cdc
    c1
    c1
    cN
    11multnc.n
    1nn0
    1nn0
    decmulnc
    @0
    cN
    @0
    cN
    cN
    cN
    11multnc.n
    nn0cni
    mulid1i
    #
    @1
    deceq12i
    eqtri
end
