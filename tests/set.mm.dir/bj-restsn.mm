include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "elrest.mm"
include "mpan.mm"
include "velsn.mm"
include "ineq1.mm"
include "sneqd.mm"
include "eleq2d.mm"
include "syl5bbr.mm"
include "rexsng.mm"
include "sylan9bbr.mm"
include "eqrdv.mm"

theorem bj-restsn
  let cA: class A
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Y e. V /\ A e. W ) -> ( { Y } |`t A ) = { ( Y i^i A ) } )

  proof
    cY
    cV
    wcel
    #
    cA
    cW
    wcel
    #
    wa
    vx
    cY
    csn
    #
    cA
    crest
    co
    #
    cY
    cA
    cin
    #
    csn
    #
    @1
    vx
    cv
    #
    @3
    wcel
    #
    @6
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    @2
    wrex
    #
    @0
    @6
    @5
    wcel
    #
    @2
    cvv
    wcel
    @1
    @7
    @11
    wb
    cY
    snex
    vy
    @6
    cA
    @2
    cvv
    cW
    elrest
    mpan
    @10
    @12
    vy
    cY
    cV
    @10
    @6
    @9
    csn
    #
    wcel
    @8
    cY
    wceq
    #
    @12
    vx
    @9
    velsn
    @14
    @13
    @5
    @6
    @14
    @9
    @4
    @8
    cY
    cA
    ineq1
    sneqd
    eleq2d
    syl5bbr
    rexsng
    sylan9bbr
    eqrdv
end
