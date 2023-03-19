include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "coprab.mm"
include "csb.mm"
include "cmpt2.mm"
include "wsbc.mm"
include "csboprabg.mm"
include "sbcan.mm"
include "sbcel12.mm"
include "csbconstg.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "sbceq2g.mm"
include "oprabbidv.mm"
include "eqtrd.mm"
include "df-mpt2.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbmpt22g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cV: class V
  let cY: class Y
  let cZ: class Z
  let vd: setvar d

  disjoint A y
  disjoint A z
  disjoint V y
  disjoint V z
  disjoint x y
  disjoint x z
  disjoint A d
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint V d
  disjoint Y d
  disjoint Z d
  disjoint d x
  assert |- ( A e. V -> [_ A / x ]_ ( y e. Y , z e. Z |-> D ) = ( y e. [_ A / x ]_ Y , z e. [_ A / x ]_ Z |-> [_ A / x ]_ D ) )

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
    wcel
    #
    wa
    #
    vd
    cv
    #
    cD
    wceq
    #
    wa
    #
    vy
    vz
    vd
    coprab
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
    wcel
    #
    wa
    #
    @6
    vx
    cA
    cD
    csb
    #
    wceq
    #
    wa
    #
    vy
    vz
    vd
    coprab
    #
    vx
    cA
    vy
    vz
    cY
    cZ
    cD
    cmpt2
    #
    csb
    vy
    vz
    @11
    @13
    @16
    cmpt2
    @0
    @10
    @8
    vx
    cA
    wsbc
    #
    vy
    vz
    vd
    coprab
    @19
    @8
    vx
    vy
    vz
    cA
    cV
    vd
    csboprabg
    @0
    @21
    @18
    vy
    vz
    vd
    @21
    @5
    vx
    cA
    wsbc
    #
    @7
    vx
    cA
    wsbc
    #
    wa
    @0
    @18
    @5
    @7
    vx
    cA
    sbcan
    @0
    @22
    @15
    @23
    @17
    @22
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
    @15
    @2
    @4
    vx
    cA
    sbcan
    @0
    @24
    @12
    @25
    @14
    @24
    vx
    cA
    @1
    csb
    #
    @11
    wcel
    @0
    @12
    vx
    cA
    @1
    cY
    sbcel12
    @0
    @26
    @1
    @11
    vx
    cA
    @1
    cV
    csbconstg
    eleq1d
    syl5bb
    @25
    vx
    cA
    @3
    csb
    #
    @13
    wcel
    @0
    @14
    vx
    cA
    @3
    cZ
    sbcel12
    @0
    @27
    @3
    @13
    vx
    cA
    @3
    cV
    csbconstg
    eleq1d
    syl5bb
    anbi12d
    syl5bb
    vx
    cA
    @6
    cD
    cV
    sbceq2g
    anbi12d
    syl5bb
    oprabbidv
    eqtrd
    vx
    cA
    @20
    @9
    vy
    vz
    vd
    cY
    cZ
    cD
    df-mpt2
    csbeq2i
    vy
    vz
    vd
    @11
    @13
    @16
    df-mpt2
    3eqtr4g
end
