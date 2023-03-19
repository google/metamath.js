include "crab.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wex.mm"
include "df-rab.mm"
include "rexeqi.mm"
include "rexab2.mm"
include "anass.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem rexrab2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralab2.1: |- ( x = y -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint ch x
  disjoint ph x
  disjoint ps y
  assert |- ( E. x e. { y e. A | ph } ps <-> E. y e. A ( ph /\ ch ) )

  proof
    wps
    vx
    wph
    vy
    cA
    crab
    #
    wrex
    wps
    vx
    vy
    cv
    cA
    wcel
    #
    wph
    wa
    #
    vy
    cab
    #
    wrex
    @2
    wch
    wa
    #
    vy
    wex
    #
    wph
    wch
    wa
    #
    vy
    cA
    wrex
    #
    wps
    vx
    @0
    @3
    wph
    vy
    cA
    df-rab
    rexeqi
    @2
    wps
    wch
    vx
    vy
    ralab2.1
    rexab2
    @5
    @1
    @6
    wa
    #
    vy
    wex
    @7
    @4
    @8
    vy
    @1
    wph
    wch
    anass
    exbii
    @6
    vy
    cA
    df-rex
    bitr4i
    3bitri
end
