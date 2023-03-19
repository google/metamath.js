include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "caddc.mm"
include "crio.mm"
include "wb.mm"
include "wa.mm"
include "subval.mm"
include "eqeq1d.mm"
include "3adant3.mm"
include "wreu.mm"
include "negeu.mm"
include "oveq2.mm"
include "riota2.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com13.mm"
include "bitr4d.mm"

theorem subadd
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A - B ) = C <-> ( B + C ) = A ) )

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
    cA
    cB
    cmin
    co
    #
    cC
    wceq
    #
    cB
    vx
    cv
    #
    caddc
    co
    #
    cA
    wceq
    #
    vx
    cc
    crio
    #
    cC
    wceq
    #
    cB
    cC
    caddc
    co
    #
    cA
    wceq
    #
    @0
    @1
    @4
    @9
    wb
    @2
    @0
    @1
    wa
    @3
    @8
    cC
    vx
    cA
    cB
    subval
    eqeq1d
    3adant3
    @2
    @1
    @0
    @11
    @9
    wb
    #
    @2
    @1
    @0
    @12
    @1
    @0
    wa
    @2
    @7
    vx
    cc
    wreu
    @12
    vx
    cB
    cA
    negeu
    @7
    @11
    vx
    cc
    cC
    @5
    cC
    wceq
    @6
    @10
    cA
    @5
    cC
    cB
    caddc
    oveq2
    eqeq1d
    riota2
    sylan2
    3impb
    3com13
    bitr4d
end
