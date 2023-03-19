include "c0.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "csuc.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "con0.mm"
include "wcel.mm"
include "0elon.mm"
include "oa0.mm"
include "ax-mp.mm"
include "oasuc.mm"
include "mpan.mm"
include "suceq.mm"
include "sylan9eq.mm"
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
include "wa.mm"
include "oalim.mm"
include "limuni.mm"
include "syl5ibr.mm"
include "tfinds.mm"

theorem oa0r
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. On -> ( (/) +o A ) = A )

  proof
    c0
    vx
    cv
    #
    coa
    co
    #
    @0
    wceq
    #
    c0
    c0
    coa
    co
    #
    c0
    wceq
    #
    c0
    vy
    cv
    #
    coa
    co
    #
    @5
    wceq
    #
    c0
    @5
    csuc
    #
    coa
    co
    #
    @8
    wceq
    #
    c0
    cA
    coa
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
    c0
    coa
    oveq2
    @12
    id
    eqeq12d
    @0
    @5
    wceq
    #
    @1
    @6
    @0
    @5
    @0
    @5
    c0
    coa
    oveq2
    @13
    id
    eqeq12d
    @0
    @8
    wceq
    #
    @1
    @9
    @0
    @8
    @0
    @8
    c0
    coa
    oveq2
    @14
    id
    eqeq12d
    @0
    cA
    wceq
    #
    @1
    @11
    @0
    cA
    @0
    cA
    c0
    coa
    oveq2
    @15
    id
    eqeq12d
    c0
    con0
    wcel
    #
    @4
    0elon
    c0
    oa0
    ax-mp
    @5
    con0
    wcel
    #
    @7
    @10
    @17
    @7
    @9
    @6
    csuc
    #
    @8
    @16
    @17
    @9
    @18
    wceq
    0elon
    c0
    @5
    oasuc
    mpan
    @6
    @5
    suceq
    sylan9eq
    ex
    @7
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
    @6
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
    @5
    ciun
    @22
    vy
    @0
    @6
    @5
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
    @16
    @23
    @20
    wa
    @24
    0elon
    vy
    c0
    @0
    cvv
    oalim
    mpan
    mpan
    @0
    limuni
    eqeq12d
    syl5ibr
    tfinds
end
