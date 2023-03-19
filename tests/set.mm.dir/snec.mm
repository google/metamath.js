include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "csn.mm"
include "wrex.mm"
include "cab.mm"
include "cqs.mm"
include "eceq1.mm"
include "eqeq2d.mm"
include "rexsn.mm"
include "abbii.mm"
include "df-qs.mm"
include "df-sn.mm"
include "3eqtr4ri.mm"

theorem snec
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume snec.1: |- A e. _V


  assert |- { [ A ] R } = ( { A } /. R )

  proof
    vy
    cv
    #
    vx
    cv
    #
    cR
    cec
    #
    wceq
    #
    vx
    cA
    csn
    #
    wrex
    #
    vy
    cab
    @0
    cA
    cR
    cec
    #
    wceq
    #
    vy
    cab
    @4
    cR
    cqs
    @6
    csn
    @5
    @7
    vy
    @3
    @7
    vx
    cA
    snec.1
    @1
    cA
    wceq
    @2
    @6
    @0
    @1
    cA
    cR
    eceq1
    eqeq2d
    rexsn
    abbii
    vx
    vy
    @4
    cR
    df-qs
    vy
    @6
    df-sn
    3eqtr4ri
end
