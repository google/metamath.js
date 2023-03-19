include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfzo.mm"
include "id.mm"
include "nn0p1nn.mm"
include "nn0re.mm"
include "ltp1d.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"

theorem fzonn0p1
  let cN: class N


  assert |- ( N e. NN0 -> N e. ( 0 ..^ ( N + 1 ) ) )

  proof
    cN
    cn0
    wcel
    #
    @0
    cN
    c1
    caddc
    co
    #
    cn
    wcel
    cN
    @1
    clt
    wbr
    cN
    cc0
    @1
    cfzo
    co
    wcel
    @0
    id
    cN
    nn0p1nn
    @0
    cN
    cN
    nn0re
    ltp1d
    cN
    @1
    elfzo0
    syl3anbrc
end
