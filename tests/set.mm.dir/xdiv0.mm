include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cxdiv.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "0re.mm"
include "rexdiv.mm"
include "mp3an1.mm"
include "cc.mm"
include "recn.mm"
include "div0.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem xdiv0
  let cA: class A


  assert |- ( ( A e. RR /\ A =/= 0 ) -> ( 0 /e A ) = 0 )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cc0
    cA
    cxdiv
    co
    #
    cc0
    cA
    cdiv
    co
    #
    cc0
    cc0
    cr
    wcel
    @0
    @1
    @2
    @3
    wceq
    0re
    cc0
    cA
    rexdiv
    mp3an1
    @0
    cA
    cc
    wcel
    @1
    @3
    cc0
    wceq
    cA
    recn
    cA
    div0
    sylan
    eqtrd
end
