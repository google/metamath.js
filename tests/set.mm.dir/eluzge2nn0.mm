include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "eluz2nn.mm"
include "nnnn0d.mm"

theorem eluzge2nn0
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> N e. NN0 )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    cN
    cN
    eluz2nn
    nnnn0d
end
