include "cn.mm"
include "cz.mm"
include "nnssz.mm"
include "sseli.mm"

theorem nnz
  let cN: class N


  assert |- ( N e. NN -> N e. ZZ )

  proof
    cn
    cz
    cN
    nnssz
    sseli
end
