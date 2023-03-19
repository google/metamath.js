include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "cc0.mm"
include "wne.mm"
include "c0.mm"
include "nnne0.mm"
include "wceq.mm"
include "cn0.mm"
include "wo.mm"
include "hashcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "necon1ad.mm"
include "impbid2.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "bitrd.mm"

theorem hashnncl
  let cA: class A


  assert |- ( A e. Fin -> ( ( # ` A ) e. NN <-> A =/= (/) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    chash
    cfv
    #
    cn
    wcel
    #
    @1
    cc0
    wne
    #
    cA
    c0
    wne
    @0
    @2
    @3
    @1
    nnne0
    @0
    @2
    @1
    cc0
    @0
    @2
    @1
    cc0
    wceq
    #
    @0
    @1
    cn0
    wcel
    @2
    @4
    wo
    cA
    hashcl
    @1
    elnn0
    sylib
    ord
    necon1ad
    impbid2
    @0
    @1
    cc0
    cA
    c0
    cA
    cfn
    hasheq0
    necon3bid
    bitrd
end
