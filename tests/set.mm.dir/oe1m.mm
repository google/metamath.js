include "c1o.mm"
include "cv.mm"
include "coe.mm"
include "co.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "con0.mm"
include "wcel.mm"
include "1on.mm"
include "oe0.mm"
include "ax-mp.mm"
include "comu.mm"
include "oesuc.mm"
include "mpan.mm"
include "oveq1.mm"
include "om1.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "ex.mm"
include "wral.mm"
include "wlim.mm"
include "ciun.mm"
include "iuneq2.mm"
include "cvv.mm"
include "vex.mm"
include "wa.mm"
include "0lt1o.mm"
include "oelim.mm"
include "mpan2.mm"
include "wne.mm"
include "0ellim.mm"
include "ne0i.mm"
include "iunconst.mm"
include "3syl.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "syl5ibr.mm"
include "tfinds.mm"

theorem oe1m
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> ( 1o ^o A ) = 1o )

  proof
    c1o
    vx
    cv
    #
    coe
    co
    #
    c1o
    wceq
    #
    c1o
    c0
    coe
    co
    #
    c1o
    wceq
    #
    c1o
    vy
    cv
    #
    coe
    co
    #
    c1o
    wceq
    #
    c1o
    @5
    csuc
    #
    coe
    co
    #
    c1o
    wceq
    #
    c1o
    cA
    coe
    co
    #
    c1o
    wceq
    vx
    vy
    cA
    @0
    c0
    wceq
    @1
    @3
    c1o
    @0
    c0
    c1o
    coe
    oveq2
    eqeq1d
    @0
    @5
    wceq
    @1
    @6
    c1o
    @0
    @5
    c1o
    coe
    oveq2
    eqeq1d
    @0
    @8
    wceq
    @1
    @9
    c1o
    @0
    @8
    c1o
    coe
    oveq2
    eqeq1d
    @0
    cA
    wceq
    @1
    @11
    c1o
    @0
    cA
    c1o
    coe
    oveq2
    eqeq1d
    c1o
    con0
    wcel
    #
    @4
    1on
    c1o
    oe0
    ax-mp
    @5
    con0
    wcel
    #
    @7
    @10
    @13
    @7
    @9
    @6
    c1o
    comu
    co
    #
    c1o
    @12
    @13
    @9
    @14
    wceq
    1on
    c1o
    @5
    oesuc
    mpan
    @7
    @14
    c1o
    c1o
    comu
    co
    #
    c1o
    @6
    c1o
    c1o
    comu
    oveq1
    @12
    @15
    c1o
    wceq
    1on
    c1o
    om1
    ax-mp
    syl6eq
    sylan9eq
    ex
    @7
    vy
    @0
    wral
    @2
    @0
    wlim
    #
    vy
    @0
    @6
    ciun
    #
    vy
    @0
    c1o
    ciun
    #
    wceq
    #
    vy
    @0
    @6
    c1o
    iuneq2
    @16
    @2
    @17
    c1o
    wceq
    @19
    @16
    @1
    @17
    c1o
    @0
    cvv
    wcel
    #
    @16
    @1
    @17
    wceq
    #
    vx
    vex
    @12
    @20
    @16
    wa
    #
    @21
    1on
    @12
    @22
    wa
    c0
    c1o
    wcel
    @21
    0lt1o
    vy
    c1o
    @0
    cvv
    oelim
    mpan2
    mpan
    mpan
    eqeq1d
    @16
    @18
    c1o
    @17
    @16
    c0
    @0
    wcel
    @0
    c0
    wne
    @18
    c1o
    wceq
    @0
    0ellim
    @0
    c0
    ne0i
    vy
    @0
    c1o
    iunconst
    3syl
    eqeq2d
    bitr4d
    syl5ibr
    tfinds
end
