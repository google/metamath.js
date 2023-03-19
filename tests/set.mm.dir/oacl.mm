include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oa0.mm"
include "ibir.mm"
include "wi.mm"
include "wa.mm"
include "suceloni.mm"
include "oasuc.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "cvv.mm"
include "vex.mm"
include "iunon.mm"
include "mpan.mm"
include "oalim.mm"
include "mpanr1.mm"
include "tfinds3.mm"
include "impcom.mm"

theorem oacl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On ) -> ( A +o B ) e. On )

  proof
    cB
    con0
    wcel
    cA
    con0
    wcel
    #
    cA
    cB
    coa
    co
    #
    con0
    wcel
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    con0
    wcel
    #
    cA
    c0
    coa
    co
    #
    con0
    wcel
    #
    cA
    vy
    cv
    #
    coa
    co
    #
    con0
    wcel
    #
    cA
    @8
    csuc
    #
    coa
    co
    #
    con0
    wcel
    #
    @2
    @0
    vx
    vy
    cB
    @3
    c0
    wceq
    @4
    @6
    con0
    @3
    c0
    cA
    coa
    oveq2
    eleq1d
    @3
    @8
    wceq
    @4
    @9
    con0
    @3
    @8
    cA
    coa
    oveq2
    eleq1d
    @3
    @11
    wceq
    @4
    @12
    con0
    @3
    @11
    cA
    coa
    oveq2
    eleq1d
    @3
    cB
    wceq
    @4
    @1
    con0
    @3
    cB
    cA
    coa
    oveq2
    eleq1d
    @0
    @7
    @0
    @6
    cA
    con0
    cA
    oa0
    eleq1d
    ibir
    @0
    @8
    con0
    wcel
    #
    @10
    @13
    wi
    @10
    @13
    @0
    @14
    wa
    #
    @9
    csuc
    #
    con0
    wcel
    @9
    suceloni
    @15
    @12
    @16
    con0
    cA
    @8
    oasuc
    eleq1d
    syl5ibr
    expcom
    @0
    @3
    wlim
    #
    @10
    vy
    @3
    wral
    #
    @5
    wi
    @18
    @5
    @0
    @17
    wa
    #
    vy
    @3
    @9
    ciun
    #
    con0
    wcel
    #
    @3
    cvv
    wcel
    #
    @18
    @21
    vx
    vex
    #
    vy
    @3
    @9
    cvv
    iunon
    mpan
    @19
    @4
    @20
    con0
    @0
    @22
    @17
    @4
    @20
    wceq
    @23
    vy
    cA
    @3
    cvv
    oalim
    mpanr1
    eleq1d
    syl5ibr
    expcom
    tfinds3
    impcom
end
