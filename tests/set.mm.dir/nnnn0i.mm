include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "nnnn0.mm"
include "ax-mp.mm"

theorem nnnn0i
  let cN: class N
  assume nnnn0i.1: |- N e. NN


  assert |- N e. NN0

  proof
    cN
    cn
    wcel
    cN
    cn0
    wcel
    nnnn0i.1
    cN
    nnnn0
    ax-mp
end
