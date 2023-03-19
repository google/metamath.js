include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "csn.mm"
include "wo.mm"
include "sspr.mm"
include "unieq.mm"
include "uni0.mm"
include "0ex.mm"
include "prid1.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "a1i.mm"
include "unisn.mm"
include "jaod.mm"
include "wa.mm"
include "unisng.mm"
include "sylan9eqr.mm"
include "prid2g.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "cun.mm"
include "cvv.mm"
include "uniprg.mm"
include "mpan.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "vex.mm"
include "elpr.mm"
include "simpr.mm"
include "ineq2d.mm"
include "in0.mm"
include "simpl.mm"
include "ineq1d.mm"
include "0in.mm"
include "ineq12.mm"
include "adantl.mm"
include "inidm.mm"
include "ccased.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "wb.mm"
include "prex.mm"
include "istopg.mm"
include "mp1i.mm"
include "mpbir2and.mm"
include "eqcomd.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem indistopon
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> { (/) , A } e. ( TopOn ` A ) )

  proof
    cA
    cV
    wcel
    #
    c0
    cA
    cpr
    #
    ctop
    wcel
    #
    cA
    @1
    cuni
    #
    wceq
    @1
    cA
    ctopon
    cfv
    wcel
    @0
    @2
    vx
    cv
    #
    @1
    wss
    #
    @4
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vx
    wal
    #
    @4
    vy
    cv
    #
    cin
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @0
    @8
    vx
    @5
    @4
    c0
    wceq
    #
    @4
    c0
    csn
    #
    wceq
    #
    wo
    #
    @4
    cA
    csn
    #
    wceq
    #
    @4
    @1
    wceq
    #
    wo
    #
    wo
    @0
    @7
    @4
    c0
    cA
    sspr
    @0
    @18
    @7
    @22
    @0
    @15
    @7
    @17
    @15
    @7
    wi
    @0
    @15
    @6
    c0
    cuni
    #
    @1
    @4
    c0
    unieq
    @23
    c0
    @1
    uni0
    c0
    cA
    0ex
    prid1
    #
    eqeltri
    syl6eqel
    a1i
    @17
    @7
    wi
    @0
    @17
    @6
    @16
    cuni
    #
    @1
    @4
    @16
    unieq
    @25
    c0
    @1
    c0
    0ex
    unisn
    @24
    eqeltri
    syl6eqel
    a1i
    jaod
    @0
    @20
    @7
    @21
    @0
    @20
    @7
    @0
    @20
    wa
    @6
    cA
    @1
    @20
    @0
    @6
    @19
    cuni
    cA
    @4
    @19
    unieq
    cA
    cV
    unisng
    sylan9eqr
    @0
    cA
    @1
    wcel
    #
    @20
    c0
    cA
    cV
    prid2g
    #
    adantr
    eqeltrd
    ex
    @0
    @21
    @7
    @0
    @21
    wa
    @6
    cA
    @1
    @21
    @0
    @6
    @3
    cA
    @4
    @1
    unieq
    @0
    @3
    c0
    cA
    cun
    #
    cA
    c0
    cvv
    wcel
    @0
    @3
    @28
    wceq
    0ex
    c0
    cA
    cvv
    cV
    uniprg
    mpan
    @28
    cA
    c0
    cun
    cA
    c0
    cA
    uncom
    cA
    un0
    eqtri
    syl6eq
    #
    sylan9eqr
    @0
    @26
    @21
    @27
    adantr
    eqeltrd
    ex
    jaod
    jaod
    syl5bi
    alrimiv
    @0
    @13
    vx
    @1
    @4
    @1
    wcel
    @15
    @4
    cA
    wceq
    #
    wo
    #
    @0
    @13
    @4
    c0
    cA
    vx
    vex
    elpr
    @0
    @31
    @13
    @0
    @31
    wa
    #
    @12
    vy
    @1
    @10
    @1
    wcel
    @10
    c0
    wceq
    #
    @10
    cA
    wceq
    #
    wo
    #
    @32
    @12
    @10
    c0
    cA
    vy
    vex
    elpr
    @0
    @31
    @35
    @12
    @0
    @15
    @33
    @30
    @34
    @12
    @15
    @33
    wa
    #
    @12
    wi
    @0
    @36
    @11
    c0
    @1
    @36
    @11
    @4
    c0
    cin
    #
    c0
    @36
    @10
    c0
    @4
    @15
    @33
    simpr
    ineq2d
    @4
    in0
    #
    syl6eq
    @24
    syl6eqel
    a1i
    @30
    @33
    wa
    #
    @12
    wi
    @0
    @39
    @11
    c0
    @1
    @39
    @11
    @37
    c0
    @39
    @10
    c0
    @4
    @30
    @33
    simpr
    ineq2d
    @38
    syl6eq
    @24
    syl6eqel
    a1i
    @15
    @34
    wa
    #
    @12
    wi
    @0
    @40
    @11
    c0
    @1
    @40
    @11
    c0
    @10
    cin
    c0
    @40
    @4
    c0
    @10
    @15
    @34
    simpl
    ineq1d
    @10
    0in
    syl6eq
    @24
    syl6eqel
    a1i
    @0
    @30
    @34
    wa
    #
    @12
    @0
    @41
    wa
    #
    @11
    cA
    @1
    @42
    @11
    cA
    cA
    cin
    #
    cA
    @41
    @11
    @43
    wceq
    @0
    @4
    cA
    @10
    cA
    ineq12
    adantl
    cA
    inidm
    syl6eq
    @0
    @26
    @41
    @27
    adantr
    eqeltrd
    ex
    ccased
    expdimp
    syl5bi
    ralrimiv
    ex
    syl5bi
    ralrimiv
    @1
    cvv
    wcel
    @2
    @9
    @14
    wa
    wb
    @0
    c0
    cA
    prex
    vx
    vy
    cvv
    @1
    istopg
    mp1i
    mpbir2and
    @0
    @3
    cA
    @29
    eqcomd
    cA
    @1
    istopon
    sylanbrc
end
