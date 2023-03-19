include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "crio.mm"
include "divval.mm"
include "3expb.mm"
include "3adant2.mm"
include "eqeq1d.mm"
include "wreu.mm"
include "wb.mm"
include "simp2.mm"
include "receu.mm"
include "oveq2.mm"
include "riota2.mm"
include "syl2anc.mm"
include "bitr4d.mm"

theorem divmul
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. CC /\ B e. CC /\ ( C e. CC /\ C =/= 0 ) ) -> ( ( A / C ) = B <-> ( C x. B ) = A ) )

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
    cC
    cdiv
    co
    #
    cB
    wceq
    cC
    vx
    cv
    #
    cmul
    co
    #
    cA
    wceq
    #
    vx
    cc
    crio
    #
    cB
    wceq
    #
    cC
    cB
    cmul
    co
    #
    cA
    wceq
    #
    @5
    @6
    @10
    cB
    @0
    @4
    @6
    @10
    wceq
    #
    @1
    @0
    @2
    @3
    @14
    vx
    cA
    cC
    divval
    3expb
    3adant2
    eqeq1d
    @5
    @1
    @9
    vx
    cc
    wreu
    #
    @13
    @11
    wb
    @0
    @1
    @4
    simp2
    @0
    @4
    @15
    @1
    @0
    @2
    @3
    @15
    vx
    cA
    cC
    receu
    3expb
    3adant2
    @9
    @13
    vx
    cc
    cB
    @7
    cB
    wceq
    @8
    @12
    cA
    @7
    cB
    cC
    cmul
    oveq2
    eqeq1d
    riota2
    syl2anc
    bitr4d
end
