include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp3.mm"
include "simp1r.mm"
include "divcl.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "simp2r.mm"
include "div23.mm"
include "syl112anc.mm"
include "divcan2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem dmdcan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) /\ C e. CC ) -> ( ( A / B ) x. ( C / A ) ) = ( C / B ) )

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
    w3a
    #
    cA
    cC
    cA
    cdiv
    co
    #
    cmul
    co
    #
    cB
    cdiv
    co
    #
    cA
    cB
    cdiv
    co
    @8
    cmul
    co
    #
    cC
    cB
    cdiv
    co
    @7
    @0
    @8
    cc
    wcel
    #
    @3
    @4
    @10
    @11
    wceq
    @0
    @1
    @5
    @6
    simp1l
    #
    @7
    @6
    @0
    @1
    @12
    @2
    @5
    @6
    simp3
    #
    @13
    @0
    @1
    @5
    @6
    simp1r
    #
    cC
    cA
    divcl
    syl3anc
    @2
    @3
    @4
    @6
    simp2l
    @2
    @3
    @4
    @6
    simp2r
    cA
    @8
    cB
    div23
    syl112anc
    @7
    @9
    cC
    cB
    cdiv
    @7
    @6
    @0
    @1
    @9
    cC
    wceq
    @14
    @13
    @15
    cC
    cA
    divcan2
    syl3anc
    oveq1d
    eqtr3d
end
