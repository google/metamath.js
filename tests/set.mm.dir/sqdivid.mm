include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "sqval.mm"
include "adantr.mm"
include "oveq1d.mm"
include "divcan3.mm"
include "3anidm12.mm"
include "eqtrd.mm"

theorem sqdivid
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( ( A ^ 2 ) / A ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    cA
    cdiv
    co
    cA
    cA
    cmul
    co
    #
    cA
    cdiv
    co
    #
    cA
    @2
    @3
    @4
    cA
    cdiv
    @0
    @3
    @4
    wceq
    @1
    cA
    sqval
    adantr
    oveq1d
    @0
    @1
    @5
    cA
    wceq
    cA
    cA
    divcan3
    3anidm12
    eqtrd
end
