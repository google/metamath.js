include "c0.mm"
include "cv.mm"
include "comu.mm"
include "co.mm"
include "wceq.mm"
include "csuc.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "om0x.mm"
include "com.mm"
include "wcel.mm"
include "coa.mm"
include "oveq1.mm"
include "con0.mm"
include "0elon.mm"
include "oa0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "peano1.mm"
include "nnmsuc.mm"
include "mpan.mm"
include "syl5ibr.mm"
include "finds.mm"

theorem nnm0r
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. _om -> ( (/) .o A ) = (/) )

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
    @3
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
    @2
    c0
    @0
    c0
    c0
    comu
    oveq2
    eqeq1d
    @0
    @3
    wceq
    @1
    @4
    c0
    @0
    @3
    c0
    comu
    oveq2
    eqeq1d
    @0
    @6
    wceq
    @1
    @7
    c0
    @0
    @6
    c0
    comu
    oveq2
    eqeq1d
    @0
    cA
    wceq
    @1
    @9
    c0
    @0
    cA
    c0
    comu
    oveq2
    eqeq1d
    c0
    om0x
    @5
    @8
    @3
    com
    wcel
    #
    @4
    c0
    coa
    co
    #
    c0
    wceq
    @5
    @11
    c0
    c0
    coa
    co
    #
    c0
    @4
    c0
    c0
    coa
    oveq1
    c0
    con0
    wcel
    @12
    c0
    wceq
    0elon
    c0
    oa0
    ax-mp
    syl6eq
    @10
    @7
    @11
    c0
    c0
    com
    wcel
    @10
    @7
    @11
    wceq
    peano1
    c0
    @3
    nnmsuc
    mpan
    eqeq1d
    syl5ibr
    finds
end
