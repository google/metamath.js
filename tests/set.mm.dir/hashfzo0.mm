include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "wceq.mm"
include "cuz.mm"
include "hashfzo.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "nn0cn.mm"
include "subid1d.mm"
include "eqtrd.mm"

theorem hashfzo0
  let cB: class B


  assert |- ( B e. NN0 -> ( # ` ( 0 ..^ B ) ) = B )

  proof
    cB
    cn0
    wcel
    #
    cc0
    cB
    cfzo
    co
    chash
    cfv
    #
    cB
    cc0
    cmin
    co
    #
    cB
    @1
    @2
    wceq
    cB
    cc0
    cuz
    cfv
    cn0
    cc0
    cB
    hashfzo
    nn0uz
    eleq2s
    @0
    cB
    cB
    nn0cn
    subid1d
    eqtrd
end
