include "cvv.mm"
include "crio.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "df-riota.mm"
include "vex.mm"
include "biantrur.mm"
include "iotabii.mm"
include "eqtr4i.mm"

theorem riotav
  let wph: wff ph
  let vx: setvar x


  assert |- ( iota_ x e. _V ph ) = ( iota x ph )

  proof
    wph
    vx
    cvv
    crio
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    cio
    wph
    vx
    cio
    wph
    vx
    cvv
    df-riota
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    biantrur
    iotabii
    eqtr4i
end
