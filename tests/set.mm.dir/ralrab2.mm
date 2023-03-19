include "crab.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "df-rab.mm"
include "raleqi.mm"
include "ralab2.mm"
include "impexp.mm"
include "albii.mm"
include "df-ral.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem ralrab2
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
  assert |- ( A. x e. { y e. A | ph } ps <-> A. y e. A ( ph -> ch ) )

  proof
    wps
    vx
    wph
    vy
    cA
    crab
    #
    wral
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
    wral
    @2
    wch
    wi
    #
    vy
    wal
    #
    wph
    wch
    wi
    #
    vy
    cA
    wral
    #
    wps
    vx
    @0
    @3
    wph
    vy
    cA
    df-rab
    raleqi
    @2
    wps
    wch
    vx
    vy
    ralab2.1
    ralab2
    @5
    @1
    @6
    wi
    #
    vy
    wal
    @7
    @4
    @8
    vy
    @1
    wph
    wch
    impexp
    albii
    @6
    vy
    cA
    df-ral
    bitr4i
    3bitri
end
