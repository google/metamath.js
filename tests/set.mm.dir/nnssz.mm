include "cn.mm"
include "cz.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "elnnz.mm"
include "simplbi.mm"
include "ssriv.mm"

theorem nnssz
  let vx: setvar x


  assert |- NN C_ ZZ

  proof
    vx
    cn
    cz
    vx
    cv
    #
    cn
    wcel
    @0
    cz
    wcel
    cc0
    @0
    clt
    wbr
    @0
    elnnz
    simplbi
    ssriv
end
