include "cn0.mm"
include "cn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "df-n0.mm"
include "nnex.mm"
include "snex.mm"
include "unex.mm"
include "eqeltri.mm"

theorem nn0ex



  assert |- NN0 e. _V

  proof
    cn0
    cn
    cc0
    csn
    #
    cun
    cvv
    df-n0
    cn
    @0
    nnex
    cc0
    snex
    unex
    eqeltri
end
