include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "simp3l.mm"
include "simp1.mm"
include "mulcld.mm"
include "divsubdir.mm"
include "syld3an1.mm"
include "divcan3.mm"
include "3expb.mm"
include "3adant2.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem subdivcomb1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( ( C x. A ) - B ) / C ) = ( A - ( B / C ) ) )

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
    cC
    cA
    cmul
    co
    #
    cB
    cmin
    co
    cC
    cdiv
    co
    #
    @6
    cC
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    cmin
    co
    #
    cA
    @9
    cmin
    co
    @6
    cc
    wcel
    @1
    @0
    @4
    @7
    @10
    wceq
    @5
    cC
    cA
    @0
    @1
    @2
    @3
    simp3l
    @0
    @1
    @4
    simp1
    mulcld
    @6
    cB
    cC
    divsubdir
    syld3an1
    @5
    @8
    cA
    @9
    cmin
    @0
    @4
    @8
    cA
    wceq
    #
    @1
    @0
    @2
    @3
    @11
    cA
    cC
    divcan3
    3expb
    3adant2
    oveq1d
    eqtrd
end
