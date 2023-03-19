include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "divmulass.mm"
include "wceq.mm"
include "mulcom.mm"
include "3adant3.mm"
include "adantr.mm"
include "oveq1d.mm"
include "simpl2.mm"
include "simpl1.mm"
include "simp3.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "divcl.mm"
include "syl.mm"
include "mulassd.mm"
include "simpr.mm"
include "divass.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem divmulasscom
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. CC /\ C e. CC ) /\ ( D e. CC /\ D =/= 0 ) ) -> ( ( A x. ( B / D ) ) x. C ) = ( B x. ( ( A x. C ) / D ) ) )

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
    w3a
    #
    cD
    cc
    wcel
    #
    cD
    cc0
    wne
    #
    wa
    #
    wa
    #
    cA
    cB
    cD
    cdiv
    co
    cmul
    co
    cC
    cmul
    co
    cA
    cB
    cmul
    co
    #
    cC
    cD
    cdiv
    co
    #
    cmul
    co
    cB
    cA
    cmul
    co
    #
    @9
    cmul
    co
    #
    cB
    cA
    cC
    cmul
    co
    cD
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cB
    cC
    cD
    divmulass
    @7
    @8
    @10
    @9
    cmul
    @3
    @8
    @10
    wceq
    #
    @6
    @0
    @1
    @14
    @2
    cA
    cB
    mulcom
    3adant3
    adantr
    oveq1d
    @7
    @11
    cB
    cA
    @9
    cmul
    co
    #
    cmul
    co
    @13
    @7
    cB
    cA
    @9
    @0
    @1
    @2
    @6
    simpl2
    @0
    @1
    @2
    @6
    simpl1
    #
    @7
    @2
    @4
    @5
    w3a
    #
    @9
    cc
    wcel
    @7
    @2
    @6
    wa
    @17
    @3
    @2
    @6
    @0
    @1
    @2
    simp3
    #
    anim1i
    @2
    @4
    @5
    3anass
    sylibr
    cC
    cD
    divcl
    syl
    mulassd
    @7
    @15
    @12
    cB
    cmul
    @7
    @12
    @15
    @7
    @0
    @2
    @6
    @12
    @15
    wceq
    @16
    @3
    @2
    @6
    @18
    adantr
    @3
    @6
    simpr
    cA
    cC
    cD
    divass
    syl3anc
    eqcomd
    oveq2d
    eqtrd
    3eqtrd
end
