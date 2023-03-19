include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "rdgsuc.mm"
include "adantl.mm"
include "suceloni.mm"
include "oav.mm"
include "sylan2.mm"
include "ovex.mm"
include "suceq.mm"
include "eqid.mm"
include "sucex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem oasuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. On ) -> ( A +o suc B ) = suc ( A +o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
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
    @1
    @8
    @10
    wceq
    @0
    cA
    cB
    @6
    rdgsuc
    adantl
    @1
    @0
    @3
    con0
    wcel
    @11
    @8
    wceq
    cB
    suceloni
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
    @14
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
    @15
    sucex
    fvmpt
    ax-mp
    @2
    @12
    @9
    @6
    vx
    cA
    cB
    oav
    fveq2d
    syl5eqr
    3eqtr4d
end
