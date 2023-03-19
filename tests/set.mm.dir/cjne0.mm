include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cj0.mm"
include "eqeq2i.mm"
include "wb.mm"
include "0cn.mm"
include "cj11.mm"
include "mpan2.mm"
include "syl5rbbr.mm"
include "necon3bid.mm"

theorem cjne0
  let cA: class A


  assert |- ( A e. CC -> ( A =/= 0 <-> ( * ` A ) =/= 0 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    cA
    ccj
    cfv
    #
    cc0
    @1
    cc0
    wceq
    @1
    cc0
    ccj
    cfv
    #
    wceq
    #
    @0
    cA
    cc0
    wceq
    #
    @2
    cc0
    @1
    cj0
    eqeq2i
    @0
    cc0
    cc
    wcel
    @3
    @4
    wb
    0cn
    cA
    cc0
    cj11
    mpan2
    syl5rbbr
    necon3bid
end
