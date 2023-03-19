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
include "cnegex2.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "oveq2.mm"
include "simprr.mm"
include "oveq1d.mm"
include "simprl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "addassd.mm"
include "addid2.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "simpl3.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "impbid1.mm"
include "rexlimddv.mm"

theorem addcan
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( A + B ) = ( A + C ) <-> B = C ) )

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
    vx
    cv
    #
    cA
    caddc
    co
    #
    cc0
    wceq
    #
    cA
    cB
    caddc
    co
    #
    cA
    cC
    caddc
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    wb
    vx
    cc
    @0
    @1
    @6
    vx
    cc
    wrex
    @2
    vx
    cA
    cnegex2
    3ad2ant1
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
    @4
    @7
    caddc
    co
    #
    @4
    @8
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
    oveq2
    @13
    @14
    cB
    @15
    cC
    @13
    @5
    cB
    caddc
    co
    cc0
    cB
    caddc
    co
    #
    @14
    cB
    @13
    @5
    cc0
    cB
    caddc
    @3
    @11
    @6
    simprr
    #
    oveq1d
    @13
    @4
    cA
    cB
    @3
    @11
    @6
    simprl
    #
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
    simpl2
    #
    addassd
    @13
    @1
    @16
    cB
    wceq
    @20
    cB
    addid2
    syl
    3eqtr3d
    @13
    @5
    cC
    caddc
    co
    cc0
    cC
    caddc
    co
    #
    @15
    cC
    @13
    @5
    cc0
    cC
    caddc
    @17
    oveq1d
    @13
    @4
    cA
    cC
    @18
    @19
    @0
    @1
    @2
    @12
    simpl3
    #
    addassd
    @13
    @2
    @21
    cC
    wceq
    @22
    cC
    addid2
    syl
    3eqtr3d
    eqeq12d
    syl5ib
    cB
    cC
    cA
    caddc
    oveq2
    impbid1
    rexlimddv
end
