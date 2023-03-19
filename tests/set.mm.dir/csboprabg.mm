include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "csb.mm"
include "wsbc.mm"
include "coprab.mm"
include "csbab.mm"
include "sbcex2.mm"
include "sbcan.mm"
include "sbcg.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "exbidv.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "df-oprab.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csboprabg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cV: class V
  let vd: setvar d
  let vc: setvar c

  disjoint A d
  disjoint A y
  disjoint A z
  disjoint V d
  disjoint V y
  disjoint V z
  disjoint d x
  disjoint x y
  disjoint x z
  disjoint A c
  disjoint c d
  disjoint c y
  disjoint c z
  disjoint V c
  disjoint c ph
  disjoint c x
  assert |- ( A e. V -> [_ A / x ]_ { <. <. y , z >. , d >. | ph } = { <. <. y , z >. , d >. | [. A / x ]. ph } )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vc
    cv
    vy
    cv
    vz
    cv
    cop
    vd
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vd
    wex
    #
    vz
    wex
    #
    vy
    wex
    #
    vc
    cab
    #
    csb
    #
    @1
    wph
    vx
    cA
    wsbc
    #
    wa
    #
    vd
    wex
    #
    vz
    wex
    #
    vy
    wex
    #
    vc
    cab
    #
    vx
    cA
    wph
    vy
    vz
    vd
    coprab
    #
    csb
    @8
    vy
    vz
    vd
    coprab
    @0
    @7
    @5
    vx
    cA
    wsbc
    #
    vc
    cab
    @13
    @5
    vx
    vc
    cA
    csbab
    @0
    @15
    @12
    vc
    @15
    @4
    vx
    cA
    wsbc
    #
    vy
    wex
    @0
    @12
    @4
    vy
    vx
    cA
    sbcex2
    @0
    @16
    @11
    vy
    @16
    @3
    vx
    cA
    wsbc
    #
    vz
    wex
    @0
    @11
    @3
    vz
    vx
    cA
    sbcex2
    @0
    @17
    @10
    vz
    @17
    @2
    vx
    cA
    wsbc
    #
    vd
    wex
    @0
    @10
    @2
    vd
    vx
    cA
    sbcex2
    @0
    @18
    @9
    vd
    @18
    @1
    vx
    cA
    wsbc
    #
    @8
    wa
    @0
    @9
    @1
    wph
    vx
    cA
    sbcan
    @0
    @19
    @1
    @8
    @1
    vx
    cA
    cV
    sbcg
    anbi1d
    syl5bb
    exbidv
    syl5bb
    exbidv
    syl5bb
    exbidv
    syl5bb
    abbidv
    syl5eq
    vx
    cA
    @14
    @6
    wph
    vy
    vz
    vd
    vc
    df-oprab
    csbeq2i
    @8
    vy
    vz
    vd
    vc
    df-oprab
    3eqtr4g
end
