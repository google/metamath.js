include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "crn.mm"
include "wcel.mm"
include "wi.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "wa.mm"
include "vex.mm"
include "brelrn.mm"
include "pm4.71ri.mm"
include "mobii.mm"
include "moanimv.mm"
include "bitri.mm"
include "albii.mm"
include "funcnv2.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem funcnv
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun `' A <-> A. y e. ran A E* x x A y )

  proof
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    @1
    cA
    crn
    #
    wcel
    #
    @3
    wi
    #
    vy
    wal
    cA
    ccnv
    wfun
    @3
    vy
    @4
    wral
    @3
    @6
    vy
    @3
    @5
    @2
    wa
    #
    vx
    wmo
    @6
    @2
    @7
    vx
    @2
    @5
    @0
    @1
    cA
    vx
    vex
    vy
    vex
    brelrn
    pm4.71ri
    mobii
    @5
    @2
    vx
    moanimv
    bitri
    albii
    vx
    vy
    cA
    funcnv2
    @3
    vy
    @4
    df-ral
    3bitr4i
end
