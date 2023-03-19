include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "syl.mm"

theorem nnrecrp
  let cN: class N


  assert |- ( N e. NN -> ( 1 / N ) e. RR+ )

  proof
    cN
    cn
    wcel
    cN
    crp
    wcel
    c1
    cN
    cdiv
    co
    crp
    wcel
    cN
    nnrp
    cN
    rpreccl
    syl
end
