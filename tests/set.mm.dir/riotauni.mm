include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "crio.mm"
include "crab.mm"
include "weu.mm"
include "wceq.mm"
include "df-reu.mm"
include "iotauni.mm"
include "sylbi.mm"
include "df-riota.mm"
include "df-rab.mm"
include "unieqi.mm"
include "3eqtr4g.mm"

theorem riotauni
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph -> ( iota_ x e. A ph ) = U. { x e. A | ph } )

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
    cuni
    #
    wph
    vx
    cA
    crio
    wph
    vx
    cA
    crab
    #
    cuni
    @0
    @1
    vx
    weu
    @2
    @4
    wceq
    wph
    vx
    cA
    df-reu
    @1
    vx
    iotauni
    sylbi
    wph
    vx
    cA
    df-riota
    @5
    @3
    wph
    vx
    cA
    df-rab
    unieqi
    3eqtr4g
end
