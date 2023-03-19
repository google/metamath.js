include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "mulcom.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "divcan3.mm"
include "eqtrd.mm"

theorem divcan4
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A x. B ) / B ) = A )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
    cB
    cdiv
    co
    cB
    cA
    cmul
    co
    #
    cB
    cdiv
    co
    cA
    @3
    @4
    @5
    cB
    cdiv
    @0
    @1
    @4
    @5
    wceq
    @2
    cA
    cB
    mulcom
    3adant3
    oveq1d
    cA
    cB
    divcan3
    eqtrd
end
