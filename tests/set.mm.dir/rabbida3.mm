include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "abbid.mm"
include "df-rab.mm"
include "3eqtr4g.mm"

theorem rabbida3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabbida3.1: |- F/ x ph
  assume rabbida3.2: |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) )


  assert |- ( ph -> { x e. A | ps } = { x e. B | ch } )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    wps
    wa
    #
    vx
    cab
    @0
    cB
    wcel
    wch
    wa
    #
    vx
    cab
    wps
    vx
    cA
    crab
    wch
    vx
    cB
    crab
    wph
    @1
    @2
    vx
    rabbida3.1
    rabbida3.2
    abbid
    wps
    vx
    cA
    df-rab
    wch
    vx
    cB
    df-rab
    3eqtr4g
end
