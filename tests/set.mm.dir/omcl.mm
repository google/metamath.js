include "con0.mm"
include "wcel.mm"
include "comu.mm"
include "co.mm"
include "cv.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "om0.mm"
include "0elon.mm"
include "syl6eqel.mm"
include "wi.mm"
include "wa.mm"
include "coa.mm"
include "oacl.mm"
include "expcom.mm"
include "adantr.mm"
include "omsuc.mm"
include "sylibrd.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "cvv.mm"
include "vex.mm"
include "iunon.mm"
include "mpan.mm"
include "omlim.mm"
include "mpanr1.mm"
include "syl5ibr.mm"
include "tfinds3.mm"
include "impcom.mm"

theorem omcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On ) -> ( A .o B ) e. On )

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
    comu
    co
    #
    con0
    wcel
    #
    cA
    vx
    cv
    #
    comu
    co
    #
    con0
    wcel
    #
    cA
    c0
    comu
    co
    #
    con0
    wcel
    cA
    vy
    cv
    #
    comu
    co
    #
    con0
    wcel
    #
    cA
    @7
    csuc
    #
    comu
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
    comu
    oveq2
    eleq1d
    @3
    @7
    wceq
    @4
    @8
    con0
    @3
    @7
    cA
    comu
    oveq2
    eleq1d
    @3
    @10
    wceq
    @4
    @11
    con0
    @3
    @10
    cA
    comu
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
    comu
    oveq2
    eleq1d
    @0
    @6
    c0
    con0
    cA
    om0
    0elon
    syl6eqel
    @0
    @7
    con0
    wcel
    #
    @9
    @12
    wi
    @0
    @13
    wa
    #
    @9
    @8
    cA
    coa
    co
    #
    con0
    wcel
    #
    @12
    @0
    @9
    @16
    wi
    @13
    @9
    @0
    @16
    @8
    cA
    oacl
    expcom
    adantr
    @14
    @11
    @15
    con0
    cA
    @7
    omsuc
    eleq1d
    sylibrd
    expcom
    @0
    @3
    wlim
    #
    @9
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
    @8
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
    @8
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
    omlim
    mpanr1
    eleq1d
    syl5ibr
    expcom
    tfinds3
    impcom
end
