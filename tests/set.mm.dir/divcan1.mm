include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "divcl.mm"
include "simp2.mm"
include "mulcomd.mm"
include "divcan2.mm"
include "eqtrd.mm"

theorem divcan1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( ( A / B ) x. B ) = A )

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
    cdiv
    co
    #
    cB
    cmul
    co
    cB
    @4
    cmul
    co
    cA
    @3
    @4
    cB
    cA
    cB
    divcl
    @0
    @1
    @2
    simp2
    mulcomd
    cA
    cB
    divcan2
    eqtrd
end
