include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "wceq.mm"
include "reccl.mm"
include "mulass.mm"
include "syl3an3.mm"
include "mulcl.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp3r.mm"
include "divrec.mm"
include "syl3anc.mm"
include "simp2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem divass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A x. B ) / C ) = ( A x. ( B / C ) ) )

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
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cB
    @7
    cmul
    co
    #
    cmul
    co
    #
    @6
    cC
    cdiv
    co
    #
    cA
    cB
    cC
    cdiv
    co
    #
    cmul
    co
    @4
    @0
    @1
    @7
    cc
    wcel
    @8
    @10
    wceq
    cC
    reccl
    cA
    cB
    @7
    mulass
    syl3an3
    @5
    @6
    cc
    wcel
    #
    @2
    @3
    @11
    @8
    wceq
    @0
    @1
    @13
    @4
    cA
    cB
    mulcl
    3adant3
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    @6
    cC
    divrec
    syl3anc
    @5
    @12
    @9
    cA
    cmul
    @5
    @1
    @2
    @3
    @12
    @9
    wceq
    @0
    @1
    @4
    simp2
    @14
    @15
    cB
    cC
    divrec
    syl3anc
    oveq2d
    3eqtr4d
end
