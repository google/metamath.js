include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "recn.mm"
include "cjreb.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem cjre
  let cA: class A


  assert |- ( A e. RR -> ( * ` A ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    ccj
    cfv
    cA
    wceq
    #
    cA
    recn
    @0
    @1
    @2
    cA
    cjreb
    biimpd
    mpcom
end
