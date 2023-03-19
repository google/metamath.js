include "cn0.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "nn0uz.mm"
include "eleq2i.mm"

theorem elnn0uz
  let cN: class N


  assert |- ( N e. NN0 <-> N e. ( ZZ>= ` 0 ) )

  proof
    cn0
    cc0
    cuz
    cfv
    cN
    nn0uz
    eleq2i
end
