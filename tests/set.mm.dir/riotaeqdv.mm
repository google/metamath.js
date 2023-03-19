include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "crio.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "iotabidv.mm"
include "df-riota.mm"
include "3eqtr4g.mm"

theorem riotaeqdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riotaeqdv.1: |- ( ph -> A = B )

  disjoint ph x
  assert |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ps ) )

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
    cio
    @0
    cB
    wcel
    #
    wps
    wa
    #
    vx
    cio
    wps
    vx
    cA
    crio
    wps
    vx
    cB
    crio
    wph
    @2
    @4
    vx
    wph
    @1
    @3
    wps
    wph
    cA
    cB
    @0
    riotaeqdv.1
    eleq2d
    anbi1d
    iotabidv
    wps
    vx
    cA
    df-riota
    wps
    vx
    cB
    df-riota
    3eqtr4g
end
