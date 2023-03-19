include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "mulcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "subeq0ad.mm"
include "simp1.mm"
include "subcl.mm"
include "3adant1.mm"
include "mul0ord.mm"
include "subdi.mm"
include "eqeq1d.mm"
include "wb.mm"
include "subeq0.mm"
include "orbi2d.mm"
include "3bitr3d.mm"
include "bitr3d.mm"

theorem mulcan1g
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A x. B ) = ( A x. C ) <-> ( A = 0 \/ B = C ) ) )

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
    cA
    cB
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wceq
    #
    @4
    @5
    wceq
    cA
    cc0
    wceq
    #
    cB
    cC
    wceq
    #
    wo
    #
    @3
    @4
    @5
    @0
    @1
    @4
    cc
    wcel
    @2
    cA
    cB
    mulcl
    3adant3
    @0
    @2
    @5
    cc
    wcel
    @1
    cA
    cC
    mulcl
    3adant2
    subeq0ad
    @3
    cA
    cB
    cC
    cmin
    co
    #
    cmul
    co
    #
    cc0
    wceq
    @8
    @11
    cc0
    wceq
    #
    wo
    @7
    @10
    @3
    cA
    @11
    @0
    @1
    @2
    simp1
    @1
    @2
    @11
    cc
    wcel
    @0
    cB
    cC
    subcl
    3adant1
    mul0ord
    @3
    @12
    @6
    cc0
    cA
    cB
    cC
    subdi
    eqeq1d
    @3
    @13
    @9
    @8
    @1
    @2
    @13
    @9
    wb
    @0
    cB
    cC
    subeq0
    3adant1
    orbi2d
    3bitr3d
    bitr3d
end
