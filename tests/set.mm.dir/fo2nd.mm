include "cvv.mm"
include "c2nd.mm"
include "wfo.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "snex.mm"
include "rnex.mm"
include "uniex.mm"
include "df-2nd.mm"
include "fnmpti.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "wcel.mm"
include "vex.mm"
include "cop.mm"
include "opex.mm"
include "op2nda.mm"
include "eqcomi.mm"
include "sneq.mm"
include "rneqd.mm"
include "unieqd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "2th.mm"
include "abbi2i.mm"
include "eqtr4i.mm"
include "df-fo.mm"
include "mpbir2an.mm"

theorem fo2nd
  let vx: setvar x
  let vy: setvar y


  assert |- 2nd : _V -onto-> _V

  proof
    cvv
    cvv
    c2nd
    wfo
    c2nd
    cvv
    wfn
    c2nd
    crn
    #
    cvv
    wceq
    vx
    cvv
    vx
    cv
    #
    csn
    #
    crn
    #
    cuni
    #
    c2nd
    @3
    @2
    @1
    snex
    rnex
    uniex
    vx
    df-2nd
    #
    fnmpti
    @0
    vy
    cv
    #
    @4
    wceq
    #
    vx
    cvv
    wrex
    #
    vy
    cab
    cvv
    vx
    vy
    cvv
    @4
    c2nd
    @5
    rnmpt
    @8
    vy
    cvv
    @6
    cvv
    wcel
    @8
    vy
    vex
    #
    @6
    @6
    cop
    #
    cvv
    wcel
    @6
    @10
    csn
    #
    crn
    #
    cuni
    #
    wceq
    #
    @8
    @6
    @6
    opex
    @13
    @6
    @6
    @6
    @9
    @9
    op2nda
    eqcomi
    @7
    @14
    vx
    @10
    cvv
    @1
    @10
    wceq
    #
    @4
    @13
    @6
    @15
    @3
    @12
    @15
    @2
    @11
    @1
    @10
    sneq
    rneqd
    unieqd
    eqeq2d
    rspcev
    mp2an
    2th
    abbi2i
    eqtr4i
    cvv
    cvv
    c2nd
    df-fo
    mpbir2an
end
