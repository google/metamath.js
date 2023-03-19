include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "cab.mm"
include "crio.mm"
include "crab.mm"
include "weu.mm"
include "df-reu.mm"
include "iotacl.mm"
include "sylbi.mm"
include "df-riota.mm"
include "df-rab.mm"
include "3eltr4g.mm"

theorem riotacl2
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. { x e. A | ph } )

  proof
    wph
    vx
    cA
    wreu
    #
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cio
    #
    @1
    vx
    cab
    #
    wph
    vx
    cA
    crio
    wph
    vx
    cA
    crab
    @0
    @1
    vx
    weu
    @2
    @3
    wcel
    wph
    vx
    cA
    df-reu
    @1
    vx
    iotacl
    sylbi
    wph
    vx
    cA
    df-riota
    wph
    vx
    cA
    df-rab
    3eltr4g
end
