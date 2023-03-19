include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "cdiv.mm"
include "co.mm"
include "1re.mm"
include "nndivre.mm"
include "mpan.mm"

theorem nnrecre
  let cN: class N


  assert |- ( N e. NN -> ( 1 / N ) e. RR )

  proof
    c1
    cr
    wcel
    cN
    cn
    wcel
    c1
    cN
    cdiv
    co
    cr
    wcel
    1re
    c1
    cN
    nndivre
    mpan
end
