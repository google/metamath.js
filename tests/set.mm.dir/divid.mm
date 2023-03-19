include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "divrec.mm"
include "3anidm12.mm"
include "recid.mm"
include "eqtrd.mm"

theorem divid
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( A / A ) = 1 )

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
    cA
    cA
    cdiv
    co
    #
    cA
    c1
    cA
    cdiv
    co
    cmul
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
    divrec
    3anidm12
    cA
    recid
    eqtrd
end
