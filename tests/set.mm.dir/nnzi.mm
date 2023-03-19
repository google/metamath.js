include "cn.mm"
include "cz.mm"
include "nnssz.mm"
include "sselii.mm"

theorem nnzi
  let cN: class N
  assume nnzi.1: |- N e. NN


  assert |- N e. ZZ

  proof
    cn
    cz
    cN
    nnssz
    nnzi.1
    sselii
end
