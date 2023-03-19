include "cn0.mm"
include "wcel.mm"
include "cneg.mm"
include "cz.mm"
include "nn0negz.mm"
include "ax-mp.mm"

theorem nn0negzi
  let cN: class N
  assume nn0negzi.1: |- N e. NN0


  assert |- -u N e. ZZ

  proof
    cN
    cn0
    wcel
    cN
    cneg
    cz
    wcel
    nn0negzi.1
    cN
    nn0negz
    ax-mp
end
