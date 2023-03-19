include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "abbid.mm"
include "df-rab.mm"
include "3eqtr4g.mm"

theorem rabbida2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabbida2.1: |- F/ x ph
  assume rabbida2.2: |- ( ph -> A = B )
  assume rabbida2.3: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> { x e. A | ps } = { x e. B | ch } )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    #
    vx
    cab
    @0
    cB
    wcel
    #
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
    @2
    @4
    vx
    rabbida2.1
    wph
    @1
    @3
    wps
    wch
    wph
    cA
    cB
    @0
    rabbida2.2
    eleq2d
    rabbida2.3
    anbi12d
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
