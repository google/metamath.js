include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "lbfzo0.mm"
include "fzoend.mm"
include "sylbir.mm"

theorem fzo0end
  let cB: class B


  assert |- ( B e. NN -> ( B - 1 ) e. ( 0 ..^ B ) )

  proof
    cB
    cn
    wcel
    cc0
    cc0
    cB
    cfzo
    co
    #
    wcel
    cB
    c1
    cmin
    co
    @0
    wcel
    cB
    lbfzo0
    cc0
    cB
    fzoend
    sylbir
end
