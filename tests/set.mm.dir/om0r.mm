include "c0.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "csuc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "om0x.mm"
include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "oveq1.mm"
include "0elon.mm"
include "omsuc.mm"
include "mpan.mm"
include "oa0.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "wral.mm"
include "wlim.mm"
include "ciun.mm"
include "iuneq2.mm"
include "iun0.mm"
include "syl6eq.mm"
include "cvv.mm"
include "vex.mm"
include "wa.mm"
include "omlim.mm"
include "tfinds.mm"

theorem om0r
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> ( (/) .o A ) = (/) )

  proof
    c0
    vx
    cv
    #
    comu
    co
    #
    c0
    wceq
    #
    c0
    c0
    comu
    co
    #
    c0
    wceq
    c0
    vy
    cv
    #
    comu
    co
    #
    c0
    wceq
    #
    c0
    @4
    csuc
    #
    comu
    co
    #
    c0
    wceq
    #
    c0
    cA
    comu
    co
    #
    c0
    wceq
    vx
    vy
    cA
    @0
    c0
    wceq
    @1
    @3
    c0
    @0
    c0
    c0
    comu
    oveq2
    eqeq1d
    @0
    @4
    wceq
    @1
    @5
    c0
    @0
    @4
    c0
    comu
    oveq2
    eqeq1d
    @0
    @7
    wceq
    @1
    @8
    c0
    @0
    @7
    c0
    comu
    oveq2
    eqeq1d
    @0
    cA
    wceq
    @1
    @10
    c0
    @0
    cA
    c0
    comu
    oveq2
    eqeq1d
    c0
    om0x
    @6
    @9
    @4
    con0
    wcel
    #
    @5
    c0
    coa
    co
    #
    c0
    c0
    coa
    co
    #
    wceq
    @5
    c0
    c0
    coa
    oveq1
    @11
    @8
    @12
    c0
    @13
    c0
    con0
    wcel
    #
    @11
    @8
    @12
    wceq
    0elon
    c0
    @4
    omsuc
    mpan
    c0
    @13
    wceq
    @11
    @13
    c0
    @14
    @13
    c0
    wceq
    0elon
    c0
    oa0
    ax-mp
    eqcomi
    a1i
    eqeq12d
    syl5ibr
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
    c0
    wceq
    @15
    @17
    vy
    @0
    c0
    ciun
    c0
    vy
    @0
    @5
    c0
    iuneq2
    vy
    @0
    iun0
    syl6eq
    @16
    @1
    @17
    c0
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
    @14
    @18
    @16
    wa
    @19
    0elon
    vy
    c0
    @0
    cvv
    omlim
    mpan
    mpan
    eqeq1d
    syl5ibr
    tfinds
end
