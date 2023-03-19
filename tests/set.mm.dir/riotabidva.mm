include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "crio.mm"
include "pm5.32da.mm"
include "iotabidv.mm"
include "df-riota.mm"
include "3eqtr4g.mm"

theorem riotabidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume riotabidva.1: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint ph x
  assert |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    wa
    #
    vx
    cio
    @0
    wch
    wa
    #
    vx
    cio
    wps
    vx
    cA
    crio
    wch
    vx
    cA
    crio
    wph
    @1
    @2
    vx
    wph
    @0
    wps
    wch
    riotabidva.1
    pm5.32da
    iotabidv
    wps
    vx
    cA
    df-riota
    wch
    vx
    cA
    df-riota
    3eqtr4g
end
