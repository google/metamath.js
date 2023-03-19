include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cxdiv.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "wceq.mm"
include "rexdiv.mm"
include "3anidm12.mm"
include "cc.mm"
include "recn.mm"
include "divid.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem xdivid
  let cA: class A


  assert |- ( ( A e. RR /\ A =/= 0 ) -> ( A /e A ) = 1 )

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
    cA
    cA
    cxdiv
    co
    #
    cA
    cA
    cdiv
    co
    #
    c1
    @0
    @1
    @2
    @3
    wceq
    cA
    cA
    rexdiv
    3anidm12
    @0
    cA
    cc
    wcel
    @1
    @3
    c1
    wceq
    cA
    recn
    cA
    divid
    sylan
    eqtrd
end
