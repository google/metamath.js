include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "divid.mm"
include "oveq1d.mm"
include "3ad2ant3.mm"
include "simp3l.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "divcl.mm"
include "3expb.mm"
include "mulid2d.mm"
include "3adant3.mm"
include "3eqtr3d.mm"

theorem divcan5
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ ( B e. CC /\ B =/= 0 ) /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( C x. A ) / ( C x. B ) ) = ( A / B ) )

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
    wa
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
    cC
    cdiv
    co
    #
    cA
    cB
    cdiv
    co
    #
    cmul
    co
    #
    c1
    @9
    cmul
    co
    #
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    cdiv
    co
    #
    @9
    @6
    @0
    @10
    @11
    wceq
    @3
    @6
    @8
    c1
    @9
    cmul
    cC
    divid
    oveq1d
    3ad2ant3
    @7
    @4
    @0
    @6
    @3
    @10
    @12
    wceq
    @0
    @3
    @4
    @5
    simp3l
    @0
    @3
    @6
    simp1
    @0
    @3
    @6
    simp3
    @0
    @3
    @6
    simp2
    cC
    cA
    cC
    cB
    divmuldiv
    syl22anc
    @0
    @3
    @11
    @9
    wceq
    @6
    @0
    @3
    wa
    @9
    @0
    @1
    @2
    @9
    cc
    wcel
    cA
    cB
    divcl
    3expb
    mulid2d
    3adant3
    3eqtr3d
end
