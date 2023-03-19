include "crab.mm"
include "bj-rabeqd.mm"
include "bj-rabbid.mm"
include "eqtrd.mm"

theorem bj-rabeqbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-rabeqbid.nf: |- F/ x ph
  assume bj-rabeqbid.1: |- ( ph -> A = B )
  assume bj-rabeqbid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> { x e. A | ps } = { x e. B | ch } )

  proof
    wph
    wps
    vx
    cA
    crab
    wps
    vx
    cB
    crab
    wch
    vx
    cB
    crab
    wph
    wps
    vx
    cA
    cB
    bj-rabeqbid.nf
    bj-rabeqbid.1
    bj-rabeqd
    wph
    wps
    wch
    vx
    cB
    bj-rabeqbid.nf
    bj-rabeqbid.2
    bj-rabbid
    eqtrd
end
