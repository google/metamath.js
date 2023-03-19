include "csb.mm"
include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wsbc.mm"
include "sbcbr.mm"
include "opabbii.mm"
include "csbopab.mm"
include "df-cnv.mm"
include "3eqtr4ri.mm"
include "csbeq2i.mm"
include "eqtr4i.mm"

theorem csbcnv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let cV: class V


  assert |- `' [_ A / x ]_ F = [_ A / x ]_ `' F

  proof
    vx
    cA
    cF
    csb
    #
    ccnv
    #
    vx
    cA
    vz
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    vz
    copab
    #
    csb
    #
    vx
    cA
    cF
    ccnv
    #
    csb
    @4
    vx
    cA
    wsbc
    #
    vy
    vz
    copab
    @2
    @3
    @0
    wbr
    #
    vy
    vz
    copab
    @6
    @1
    @8
    @9
    vy
    vz
    vx
    cA
    @2
    @3
    cF
    sbcbr
    opabbii
    @4
    vx
    vy
    vz
    cA
    csbopab
    vy
    vz
    @0
    df-cnv
    3eqtr4ri
    vx
    cA
    @7
    @5
    vy
    vz
    cF
    df-cnv
    csbeq2i
    eqtr4i
end
