include "cn0.mm"
include "clt.mm"
include "cpred.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "nn0uz.mm"
include "predeq2.mm"
include "ax-mp.mm"
include "preduz.mm"
include "syl5eq.mm"
include "eleq2s.mm"

theorem prednn0
  let cN: class N


  assert |- ( N e. NN0 -> Pred ( < , NN0 , N ) = ( 0 ... ( N - 1 ) ) )

  proof
    cn0
    clt
    cN
    cpred
    #
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    wceq
    cN
    cc0
    cuz
    cfv
    #
    cn0
    cN
    @2
    wcel
    @0
    @2
    clt
    cN
    cpred
    #
    @1
    cn0
    @2
    wceq
    @0
    @3
    wceq
    nn0uz
    cn0
    @2
    clt
    cN
    predeq2
    ax-mp
    cc0
    cN
    preduz
    syl5eq
    nn0uz
    eleq2s
end
