include "wcel.mm"
include "cab.mm"
include "csb.mm"
include "wsbc.mm"
include "cv.mm"
include "sbccom.mm"
include "wsb.mm"
include "df-clab.mm"
include "sbsbc.mm"
include "bitri.mm"
include "sbcbii.mm"
include "3bitr4i.mm"
include "wb.mm"
include "sbcel2.mm"
include "a1i.mm"
include "syl5rbb.mm"
include "eqrdv.mm"

theorem csbabgOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vz: setvar z

  disjoint A y
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint x z
  disjoint V z
  assert |- ( A e. V -> [_ A / x ]_ { y | ph } = { y | [. A / x ]. ph } )

  proof
    cA
    cV
    wcel
    #
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
    @4
    wcel
    #
    @5
    @1
    wcel
    #
    vx
    cA
    wsbc
    #
    @0
    @5
    @2
    wcel
    #
    @3
    vy
    @5
    wsbc
    #
    wph
    vy
    @5
    wsbc
    #
    vx
    cA
    wsbc
    @6
    @8
    wph
    vy
    vx
    @5
    cA
    sbccom
    @6
    @3
    vy
    vz
    wsb
    @10
    @3
    vz
    vy
    df-clab
    @3
    vy
    vz
    sbsbc
    bitri
    @7
    @11
    vx
    cA
    @7
    wph
    vy
    vz
    wsb
    @11
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
    3bitr4i
    @8
    @9
    wb
    @0
    vx
    cA
    @5
    @1
    sbcel2
    a1i
    syl5rbb
    eqrdv
end
