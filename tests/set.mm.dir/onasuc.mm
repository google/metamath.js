include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wa.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "frsuc.mm"
include "adantl.mm"
include "peano2.mm"
include "fvres.mm"
include "syl.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "nnon.mm"
include "suceloni.mm"
include "oav.mm"
include "sylan2.mm"
include "ovex.mm"
include "suceq.mm"
include "eqid.mm"
include "sucex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem onasuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. _om ) -> ( A +o suc B ) = suc ( A +o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cB
    csuc
    #
    vx
    cvv
    vx
    cv
    #
    csuc
    #
    cmpt
    #
    cA
    crdg
    #
    cfv
    #
    cB
    @7
    cfv
    #
    @6
    cfv
    #
    cA
    @3
    coa
    co
    #
    cA
    cB
    coa
    co
    #
    csuc
    #
    @2
    @3
    @7
    com
    cres
    #
    cfv
    #
    cB
    @14
    cfv
    #
    @6
    cfv
    #
    @8
    @10
    @1
    @15
    @17
    wceq
    @0
    cA
    cB
    @6
    frsuc
    adantl
    @2
    @3
    com
    wcel
    #
    @15
    @8
    wceq
    @1
    @18
    @0
    cB
    peano2
    adantl
    @3
    com
    @7
    fvres
    syl
    @2
    @16
    @9
    @6
    @1
    @16
    @9
    wceq
    @0
    cB
    com
    @7
    fvres
    adantl
    fveq2d
    3eqtr3d
    @1
    @0
    @3
    con0
    wcel
    #
    @11
    @8
    wceq
    @1
    cB
    con0
    wcel
    #
    @19
    cB
    nnon
    #
    cB
    suceloni
    syl
    vx
    cA
    @3
    oav
    sylan2
    @2
    @13
    @12
    @6
    cfv
    #
    @10
    @12
    cvv
    wcel
    @22
    @13
    wceq
    cA
    cB
    coa
    ovex
    #
    vx
    @12
    @5
    @13
    cvv
    @6
    @4
    @12
    suceq
    @6
    eqid
    @12
    @23
    sucex
    fvmpt
    ax-mp
    @2
    @12
    @9
    @6
    @1
    @0
    @20
    @12
    @9
    wceq
    @21
    vx
    cA
    cB
    oav
    sylan2
    fveq2d
    syl5eqr
    3eqtr4d
end
