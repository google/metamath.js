include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "csuc.mm"
include "cvv.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cfv.mm"
include "comu.mm"
include "wceq.mm"
include "rdgsuc.mm"
include "adantl.mm"
include "suceloni.mm"
include "omv.mm"
include "sylan2.mm"
include "ovex.mm"
include "oveq1.mm"
include "eqid.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem omsuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. On ) -> ( A .o suc B ) = ( ( A .o B ) +o A ) )

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
    cA
    coa
    co
    #
    cmpt
    #
    c0
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
    comu
    co
    #
    cA
    cB
    comu
    co
    #
    cA
    coa
    co
    #
    @1
    @8
    @10
    wceq
    @0
    c0
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
    omv
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
    comu
    ovex
    vx
    @12
    @5
    @13
    cvv
    @6
    @4
    @12
    cA
    coa
    oveq1
    @6
    eqid
    @12
    cA
    coa
    ovex
    fvmpt
    ax-mp
    @2
    @12
    @9
    @6
    vx
    cA
    cB
    omv
    fveq2d
    syl5eqr
    3eqtr4d
end
