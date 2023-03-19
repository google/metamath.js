include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "ctop.mm"
include "wb.mm"
include "sn0top.mm"
include "elrest.mm"
include "mpan.mm"
include "0ex.mm"
include "ineq1.mm"
include "0in.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "rexsn.mm"
include "velsn.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "eqrdv.mm"

theorem restsn
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( { (/) } |`t A ) = { (/) } )

  proof
    cA
    cV
    wcel
    #
    vx
    c0
    csn
    #
    cA
    crest
    co
    #
    @1
    @0
    vx
    cv
    #
    @2
    wcel
    #
    @3
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    @1
    wrex
    #
    @3
    @1
    wcel
    #
    @1
    ctop
    wcel
    @0
    @4
    @8
    wb
    sn0top
    vy
    @3
    cA
    @1
    ctop
    cV
    elrest
    mpan
    @8
    @3
    c0
    wceq
    #
    @9
    @7
    @10
    vy
    c0
    0ex
    @5
    c0
    wceq
    #
    @6
    c0
    @3
    @11
    @6
    c0
    cA
    cin
    c0
    @5
    c0
    cA
    ineq1
    cA
    0in
    syl6eq
    eqeq2d
    rexsn
    vx
    c0
    velsn
    bitr4i
    syl6bb
    eqrdv
end
