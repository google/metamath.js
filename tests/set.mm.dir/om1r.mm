include "c1o.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "om0x.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "1on.mm"
include "omsuc.mm"
include "mpan.mm"
include "oveq1.mm"
include "sylan9eq.mm"
include "oa1suc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "ex.mm"
include "wral.mm"
include "wlim.mm"
include "ciun.mm"
include "cuni.mm"
include "iuneq2.mm"
include "uniiun.mm"
include "syl6eqr.mm"
include "cvv.mm"
include "vex.mm"
include "omlim.mm"
include "limuni.mm"
include "syl5ibr.mm"
include "tfinds.mm"

theorem om1r
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> ( 1o .o A ) = A )

  proof
    c1o
    vx
    cv
    #
    comu
    co
    #
    @0
    wceq
    #
    c1o
    c0
    comu
    co
    #
    c0
    wceq
    c1o
    vy
    cv
    #
    comu
    co
    #
    @4
    wceq
    #
    c1o
    @4
    csuc
    #
    comu
    co
    #
    @7
    wceq
    #
    c1o
    cA
    comu
    co
    #
    cA
    wceq
    vx
    vy
    cA
    @0
    c0
    wceq
    #
    @1
    @3
    @0
    c0
    @0
    c0
    c1o
    comu
    oveq2
    @11
    id
    eqeq12d
    @0
    @4
    wceq
    #
    @1
    @5
    @0
    @4
    @0
    @4
    c1o
    comu
    oveq2
    @12
    id
    eqeq12d
    @0
    @7
    wceq
    #
    @1
    @8
    @0
    @7
    @0
    @7
    c1o
    comu
    oveq2
    @13
    id
    eqeq12d
    @0
    cA
    wceq
    #
    @1
    @10
    @0
    cA
    @0
    cA
    c1o
    comu
    oveq2
    @14
    id
    eqeq12d
    c1o
    om0x
    @4
    con0
    wcel
    #
    @6
    @9
    @15
    @6
    wa
    @8
    @4
    c1o
    coa
    co
    #
    @7
    @15
    @6
    @8
    @5
    c1o
    coa
    co
    #
    @16
    c1o
    con0
    wcel
    #
    @15
    @8
    @17
    wceq
    1on
    c1o
    @4
    omsuc
    mpan
    @5
    @4
    c1o
    coa
    oveq1
    sylan9eq
    @15
    @16
    @7
    wceq
    @6
    @4
    oa1suc
    adantr
    eqtrd
    ex
    @6
    vy
    @0
    wral
    #
    @2
    @0
    wlim
    #
    vy
    @0
    @5
    ciun
    #
    @0
    cuni
    #
    wceq
    @19
    @21
    vy
    @0
    @4
    ciun
    @22
    vy
    @0
    @5
    @4
    iuneq2
    vy
    @0
    uniiun
    syl6eqr
    @20
    @1
    @21
    @0
    @22
    @0
    cvv
    wcel
    #
    @20
    @1
    @21
    wceq
    #
    vx
    vex
    @18
    @23
    @20
    wa
    @24
    1on
    vy
    c1o
    @0
    cvv
    omlim
    mpan
    mpan
    @0
    limuni
    eqeq12d
    syl5ibr
    tfinds
end
