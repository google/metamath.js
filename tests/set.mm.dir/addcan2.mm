include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "wrex.mm"
include "cnegex.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "oveq1.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simprl.mm"
include "addassd.mm"
include "simprr.mm"
include "oveq2d.mm"
include "addid1.mm"
include "syl.mm"
include "3eqtrd.mm"
include "simpl2.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "impbid1.mm"
include "rexlimddv.mm"

theorem addcan2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + C ) = ( B + C ) <-> A = B ) )

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
    cC
    vx
    cv
    #
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wb
    vx
    cc
    @2
    @0
    @6
    vx
    cc
    wrex
    @1
    vx
    cC
    cnegex
    3ad2ant3
    @3
    @4
    cc
    wcel
    #
    @6
    wa
    #
    wa
    #
    @9
    @10
    @9
    @7
    @4
    caddc
    co
    #
    @8
    @4
    caddc
    co
    #
    wceq
    @13
    @10
    @7
    @8
    @4
    caddc
    oveq1
    @13
    @14
    cA
    @15
    cB
    @13
    @14
    cA
    @5
    caddc
    co
    cA
    cc0
    caddc
    co
    #
    cA
    @13
    cA
    cC
    @4
    @0
    @1
    @2
    @12
    simpl1
    #
    @0
    @1
    @2
    @12
    simpl3
    #
    @3
    @11
    @6
    simprl
    #
    addassd
    @13
    @5
    cc0
    cA
    caddc
    @3
    @11
    @6
    simprr
    #
    oveq2d
    @13
    @0
    @16
    cA
    wceq
    @17
    cA
    addid1
    syl
    3eqtrd
    @13
    @15
    cB
    @5
    caddc
    co
    cB
    cc0
    caddc
    co
    #
    cB
    @13
    cB
    cC
    @4
    @0
    @1
    @2
    @12
    simpl2
    #
    @18
    @19
    addassd
    @13
    @5
    cc0
    cB
    caddc
    @20
    oveq2d
    @13
    @1
    @21
    cB
    wceq
    @22
    cB
    addid1
    syl
    3eqtrd
    eqeq12d
    syl5ib
    cA
    cB
    cC
    caddc
    oveq1
    impbid1
    rexlimddv
end
