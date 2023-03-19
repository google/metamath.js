include "cab.mm"
include "csb.mm"
include "wsbc.mm"
include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "sbsbc.mm"
include "bitri.mm"
include "sbccom.mm"
include "sbcbii.mm"
include "bitr4i.mm"
include "sbcel2.mm"
include "3bitrri.mm"
include "eqriv.mm"

theorem csbab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint A y
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint x z
  assert |- [_ A / x ]_ { y | ph } = { y | [. A / x ]. ph }

  proof
    vz
    vx
    cA
    wph
    vy
    cab
    #
    csb
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    vz
    cv
    #
    @3
    wcel
    #
    @2
    vy
    @4
    wsbc
    #
    @4
    @0
    wcel
    #
    vx
    cA
    wsbc
    #
    @4
    @1
    wcel
    @5
    @2
    vy
    vz
    wsb
    @6
    @2
    vz
    vy
    df-clab
    @2
    vy
    vz
    sbsbc
    bitri
    @6
    wph
    vy
    @4
    wsbc
    #
    vx
    cA
    wsbc
    @8
    wph
    vy
    vx
    @4
    cA
    sbccom
    @7
    @9
    vx
    cA
    @7
    wph
    vy
    vz
    wsb
    @9
    wph
    vz
    vy
    df-clab
    wph
    vy
    vz
    sbsbc
    bitri
    sbcbii
    bitr4i
    vx
    cA
    @4
    @0
    sbcel2
    3bitrri
    eqriv
end
