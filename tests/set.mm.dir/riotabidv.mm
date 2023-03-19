include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "crio.mm"
include "anbi2d.mm"
include "iotabidv.mm"
include "df-riota.mm"
include "3eqtr4g.mm"

theorem riotabidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  assume riotabidv.1: |- ( ph -> ( ps <-> ch ) )

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
    wps
    wch
    @0
    riotabidv.1
    anbi2d
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
