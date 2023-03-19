include "cn.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "nnuz.mm"
include "eleq2i.mm"

theorem elnnuz
  let cN: class N


  assert |- ( N e. NN <-> N e. ( ZZ>= ` 1 ) )

  proof
    cn
    c1
    cuz
    cfv
    cN
    nnuz
    eleq2i
end
