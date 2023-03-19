include "con0.mm"
include "wcel.mm"
include "com.mm"
include "wa.mm"
include "csuc.mm"
include "comu.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "coa.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "peano2.mm"
include "nnon.mm"
include "syl.mm"
include "omv.mm"
include "sylan2.mm"
include "adantl.mm"
include "fvres.mm"
include "eqtr4d.mm"
include "ovex.mm"
include "oveq1.mm"
include "eqid.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "frsuc.mm"

theorem onmsuc
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. On /\ B e. _om ) -> ( A .o suc B ) = ( ( A .o B ) +o A ) )

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
    cA
    cB
    csuc
    #
    comu
    co
    #
    @3
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
    com
    cres
    #
    cfv
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
    @2
    @4
    @3
    @8
    cfv
    #
    @10
    @1
    @0
    @3
    con0
    wcel
    #
    @4
    @13
    wceq
    @1
    @3
    com
    wcel
    #
    @14
    cB
    peano2
    #
    @3
    nnon
    syl
    vx
    cA
    @3
    omv
    sylan2
    @2
    @15
    @10
    @13
    wceq
    @1
    @15
    @0
    @16
    adantl
    @3
    com
    @8
    fvres
    syl
    eqtr4d
    @2
    @12
    cB
    @9
    cfv
    #
    @7
    cfv
    #
    @10
    @2
    @12
    @11
    @7
    cfv
    #
    @18
    @11
    cvv
    wcel
    @19
    @12
    wceq
    cA
    cB
    comu
    ovex
    vx
    @11
    @6
    @12
    cvv
    @7
    @5
    @11
    cA
    coa
    oveq1
    @7
    eqid
    @11
    cA
    coa
    ovex
    fvmpt
    ax-mp
    @2
    @11
    @17
    @7
    @2
    @11
    cB
    @8
    cfv
    #
    @17
    @1
    @0
    cB
    con0
    wcel
    @11
    @20
    wceq
    cB
    nnon
    vx
    cA
    cB
    omv
    sylan2
    @1
    @17
    @20
    wceq
    @0
    cB
    com
    @8
    fvres
    adantl
    eqtr4d
    fveq2d
    syl5eqr
    @1
    @10
    @18
    wceq
    @0
    c0
    cB
    @7
    frsuc
    adantl
    eqtr4d
    eqtr4d
end
