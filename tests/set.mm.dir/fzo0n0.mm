include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "cn.mm"
include "fzon0.mm"
include "lbfzo0.mm"
include "bitri.mm"

theorem fzo0n0
  let cA: class A


  assert |- ( ( 0 ..^ A ) =/= (/) <-> A e. NN )

  proof
    cc0
    cA
    cfzo
    co
    #
    c0
    wne
    cc0
    @0
    wcel
    cA
    cn
    wcel
    cc0
    cA
    fzon0
    cA
    lbfzo0
    bitri
end
