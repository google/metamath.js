include "cvv.mm"
include "wcel.mm"
include "c2nd.mm"
include "cfv.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "cv.mm"
include "sneq.mm"
include "rneqd.mm"
include "unieqd.mm"
include "df-2nd.mm"
include "snex.mm"
include "rnex.mm"
include "uniex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "snprc.mm"
include "biimpi.mm"
include "rn0.mm"
include "syl6eq.mm"
include "uni0.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem 2ndval
  let cA: class A
  let vx: setvar x


  assert |- ( 2nd ` A ) = U. ran { A }

  proof
    cA
    cvv
    wcel
    #
    cA
    c2nd
    cfv
    #
    cA
    csn
    #
    crn
    #
    cuni
    #
    wceq
    vx
    cA
    vx
    cv
    #
    csn
    #
    crn
    #
    cuni
    @4
    cvv
    c2nd
    @5
    cA
    wceq
    #
    @7
    @3
    @8
    @6
    @2
    @5
    cA
    sneq
    rneqd
    unieqd
    vx
    df-2nd
    @3
    @2
    cA
    snex
    rnex
    uniex
    fvmpt
    @0
    wn
    #
    @1
    c0
    @4
    cA
    c2nd
    fvprc
    @9
    @4
    c0
    cuni
    c0
    @9
    @3
    c0
    @9
    @3
    c0
    crn
    c0
    @9
    @2
    c0
    @9
    @2
    c0
    wceq
    cA
    snprc
    biimpi
    rneqd
    rn0
    syl6eq
    unieqd
    uni0
    syl6eq
    eqtr4d
    pm2.61i
end
