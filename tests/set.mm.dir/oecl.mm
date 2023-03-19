include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "oveq2.mm"
include "c1o.mm"
include "oe0m0.mm"
include "1on.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wa.mm"
include "oe0m1.mm"
include "biimpa.mm"
include "0elon.mm"
include "adantll.mm"
include "oe0lem.mm"
include "anidms.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "wi.mm"
include "cv.mm"
include "csuc.mm"
include "oe0.mm"
include "adantr.mm"
include "comu.mm"
include "omcl.mm"
include "expcom.mm"
include "oesuc.mm"
include "sylibrd.mm"
include "adantrd.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "cvv.mm"
include "vex.mm"
include "iunon.mm"
include "mpan.mm"
include "oelim.mm"
include "mpanlr1.mm"
include "anasss.mm"
include "an12s.mm"
include "ex.mm"
include "tfinds3.mm"
include "expd.mm"
include "com12.mm"
include "imp31.mm"

theorem oecl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. On /\ B e. On ) -> ( A ^o B ) e. On )

  proof
    cB
    con0
    wcel
    #
    cA
    cB
    coe
    co
    #
    con0
    wcel
    #
    cA
    cA
    c0
    wceq
    #
    @0
    @2
    @0
    @2
    @3
    c0
    cB
    coe
    co
    #
    con0
    wcel
    #
    @0
    @5
    @0
    @5
    cB
    cB
    c0
    wceq
    #
    @5
    @0
    @6
    @4
    c0
    c0
    coe
    co
    #
    con0
    cB
    c0
    c0
    coe
    oveq2
    @7
    c1o
    con0
    oe0m0
    1on
    eqeltri
    syl6eqel
    adantl
    @0
    c0
    cB
    wcel
    #
    @5
    @0
    @0
    @8
    wa
    @4
    c0
    con0
    @0
    @8
    @4
    c0
    wceq
    cB
    oe0m1
    biimpa
    0elon
    syl6eqel
    adantll
    oe0lem
    anidms
    @3
    @1
    @4
    con0
    cA
    c0
    cB
    coe
    oveq1
    eleq1d
    syl5ibr
    impcom
    cA
    con0
    wcel
    #
    @0
    c0
    cA
    wcel
    #
    @2
    @0
    @9
    @10
    @2
    wi
    @0
    @9
    @10
    @2
    cA
    vx
    cv
    #
    coe
    co
    #
    con0
    wcel
    #
    cA
    c0
    coe
    co
    #
    con0
    wcel
    #
    cA
    vy
    cv
    #
    coe
    co
    #
    con0
    wcel
    #
    cA
    @16
    csuc
    #
    coe
    co
    #
    con0
    wcel
    #
    @2
    @9
    @10
    wa
    #
    vx
    vy
    cB
    @11
    c0
    wceq
    @12
    @14
    con0
    @11
    c0
    cA
    coe
    oveq2
    eleq1d
    @11
    @16
    wceq
    @12
    @17
    con0
    @11
    @16
    cA
    coe
    oveq2
    eleq1d
    @11
    @19
    wceq
    @12
    @20
    con0
    @11
    @19
    cA
    coe
    oveq2
    eleq1d
    @11
    cB
    wceq
    @12
    @1
    con0
    @11
    cB
    cA
    coe
    oveq2
    eleq1d
    @9
    @15
    @10
    @9
    @14
    c1o
    con0
    cA
    oe0
    1on
    syl6eqel
    adantr
    @16
    con0
    wcel
    #
    @9
    @18
    @21
    wi
    #
    @10
    @9
    @23
    @24
    @9
    @23
    wa
    #
    @18
    @17
    cA
    comu
    co
    #
    con0
    wcel
    #
    @21
    @9
    @18
    @27
    wi
    @23
    @18
    @9
    @27
    @17
    cA
    omcl
    expcom
    adantr
    @25
    @20
    @26
    con0
    cA
    @16
    oesuc
    eleq1d
    sylibrd
    expcom
    adantrd
    @11
    wlim
    #
    @22
    @18
    vy
    @11
    wral
    #
    @13
    wi
    @29
    @13
    @28
    @22
    wa
    #
    vy
    @11
    @17
    ciun
    #
    con0
    wcel
    #
    @11
    cvv
    wcel
    #
    @29
    @32
    vx
    vex
    #
    vy
    @11
    @17
    cvv
    iunon
    mpan
    @30
    @12
    @31
    con0
    @9
    @28
    @10
    @12
    @31
    wceq
    #
    @9
    @28
    @10
    @35
    @9
    @33
    @28
    @10
    @35
    @34
    vy
    cA
    @11
    cvv
    oelim
    mpanlr1
    anasss
    an12s
    eleq1d
    syl5ibr
    ex
    tfinds3
    expd
    com12
    imp31
    oe0lem
end
