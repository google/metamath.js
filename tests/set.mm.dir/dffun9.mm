include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "cdm.mm"
include "wral.mm"
include "wa.mm"
include "crn.mm"
include "wrmo.mm"
include "dffun7.mm"
include "wcel.mm"
include "vex.mm"
include "brelrn.mm"
include "pm4.71ri.mm"
include "mobii.mm"
include "df-rmo.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dffun9
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Fun A <-> ( Rel A /\ A. x e. dom A E* y e. ran A x A y ) )

  proof
    cA
    wfun
    cA
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    vy
    wmo
    #
    vx
    cA
    cdm
    #
    wral
    #
    wa
    @0
    @3
    vy
    cA
    crn
    #
    wrmo
    #
    vx
    @5
    wral
    #
    wa
    vx
    vy
    cA
    dffun7
    @6
    @9
    @0
    @4
    @8
    vx
    @5
    @4
    @2
    @7
    wcel
    #
    @3
    wa
    #
    vy
    wmo
    @8
    @3
    @11
    vy
    @3
    @10
    @1
    @2
    cA
    vx
    vex
    vy
    vex
    brelrn
    pm4.71ri
    mobii
    @3
    vy
    @7
    df-rmo
    bitr4i
    ralbii
    anbi2i
    bitri
end
