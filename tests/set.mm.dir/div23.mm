include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "mulcom.mm"
include "oveq1d.mm"
include "3adant3.mm"
include "divass.mm"
include "3com12.mm"
include "simp2.mm"
include "divcl.mm"
include "3expb.mm"
include "3adant2.mm"
include "mulcomd.mm"
include "3eqtrd.mm"

theorem div23
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A x. B ) / C ) = ( ( A / C ) x. B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
    cC
    cdiv
    co
    #
    cB
    cA
    cmul
    co
    #
    cC
    cdiv
    co
    #
    cB
    cA
    cC
    cdiv
    co
    #
    cmul
    co
    #
    @10
    cB
    cmul
    co
    @0
    @1
    @7
    @9
    wceq
    @4
    @0
    @1
    wa
    @6
    @8
    cC
    cdiv
    cA
    cB
    mulcom
    oveq1d
    3adant3
    @1
    @0
    @4
    @9
    @11
    wceq
    cB
    cA
    cC
    divass
    3com12
    @5
    cB
    @10
    @0
    @1
    @4
    simp2
    @0
    @4
    @10
    cc
    wcel
    #
    @1
    @0
    @2
    @3
    @12
    cA
    cC
    divcl
    3expb
    3adant2
    mulcomd
    3eqtrd
end
