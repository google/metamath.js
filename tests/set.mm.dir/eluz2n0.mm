include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "eluz2nn.mm"
include "nnne0d.mm"

theorem eluz2n0
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> N =/= 0 )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    cN
    cN
    eluz2nn
    nnne0d
end
