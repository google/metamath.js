include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "csb.mm"
include "cmpt.mm"
include "wsbc.mm"
include "csbopab.mm"
include "sbcan.mm"
include "sbcel12.mm"
include "csbconstg.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "sbceq2g.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "syl5eq.mm"
include "df-mpt.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbmpt12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vz: setvar z

  disjoint A y
  disjoint V y
  disjoint Y y
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint V z
  disjoint Y z
  disjoint Z z
  disjoint x z
  assert |- ( A e. V -> [_ A / x ]_ ( y e. Y |-> Z ) = ( y e. [_ A / x ]_ Y |-> [_ A / x ]_ Z ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vy
    cv
    #
    cY
    wcel
    #
    vz
    cv
    #
    cZ
    wceq
    #
    wa
    #
    vy
    vz
    copab
    #
    csb
    #
    @1
    vx
    cA
    cY
    csb
    #
    wcel
    #
    @3
    vx
    cA
    cZ
    csb
    #
    wceq
    #
    wa
    #
    vy
    vz
    copab
    #
    vx
    cA
    vy
    cY
    cZ
    cmpt
    #
    csb
    vy
    @8
    @10
    cmpt
    @0
    @7
    @5
    vx
    cA
    wsbc
    #
    vy
    vz
    copab
    @13
    @5
    vx
    vy
    vz
    cA
    csbopab
    @0
    @15
    @12
    vy
    vz
    @15
    @2
    vx
    cA
    wsbc
    #
    @4
    vx
    cA
    wsbc
    #
    wa
    @0
    @12
    @2
    @4
    vx
    cA
    sbcan
    @0
    @16
    @9
    @17
    @11
    @16
    vx
    cA
    @1
    csb
    #
    @8
    wcel
    @0
    @9
    vx
    cA
    @1
    cY
    sbcel12
    @0
    @18
    @1
    @8
    vx
    cA
    @1
    cV
    csbconstg
    eleq1d
    syl5bb
    vx
    cA
    @3
    cZ
    cV
    sbceq2g
    anbi12d
    syl5bb
    opabbidv
    syl5eq
    vx
    cA
    @14
    @6
    vy
    vz
    cY
    cZ
    df-mpt
    csbeq2i
    vy
    vz
    @8
    @10
    df-mpt
    3eqtr4g
end
