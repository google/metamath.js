include "cvv.mm"
include "wnel.mm"
include "cc0.mm"
include "cn.mm"
include "wo.mm"
include "cclwwlkn.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "0nnn.mm"
include "nelir.mm"
include "olci.mm"
include "clwwlkneq0.mm"
include "ax-mp.mm"

theorem clwwlkn0OLD
  let cG: class G


  assert |- ( 0 ClWWalksN G ) = (/)

  proof
    cG
    cvv
    wnel
    #
    cc0
    cn
    wnel
    #
    wo
    cc0
    cG
    cclwwlkn
    co
    c0
    wceq
    @1
    @0
    cc0
    cn
    0nnn
    nelir
    olci
    cG
    cc0
    clwwlkneq0
    ax-mp
end
