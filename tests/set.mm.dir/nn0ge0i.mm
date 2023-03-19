include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "ax-mp.mm"

theorem nn0ge0i
  let cN: class N
  assume nn0ge0i.1: |- N e. NN0


  assert |- 0 <_ N

  proof
    cN
    cn0
    wcel
    cc0
    cN
    cle
    wbr
    nn0ge0i.1
    cN
    nn0ge0
    ax-mp
end
