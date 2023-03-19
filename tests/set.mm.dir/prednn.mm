include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "cpred.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wceq.mm"
include "nnuz.mm"
include "predeq2.mm"
include "ax-mp.mm"
include "elnnuz.mm"
include "preduz.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem prednn
  let cN: class N


  assert |- ( N e. NN -> Pred ( < , NN , N ) = ( 1 ... ( N - 1 ) ) )

  proof
    cN
    cn
    wcel
    #
    cn
    clt
    cN
    cpred
    #
    c1
    cuz
    cfv
    #
    clt
    cN
    cpred
    #
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    cn
    @2
    wceq
    @1
    @3
    wceq
    nnuz
    cn
    @2
    clt
    cN
    predeq2
    ax-mp
    @0
    cN
    @2
    wcel
    @3
    @4
    wceq
    cN
    elnnuz
    c1
    cN
    preduz
    sylbi
    syl5eq
end
