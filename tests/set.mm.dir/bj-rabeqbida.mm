include "crab.mm"
include "bj-rabbida.mm"
include "bj-rabeqd.mm"
include "eqtrd.mm"

theorem bj-rabeqbida
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-rabeqbida.nf: |- F/ x ph
  assume bj-rabeqbida.1: |- ( ph -> A = B )
  assume bj-rabeqbida.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )


  assert |- ( ph -> { x e. A | ps } = { x e. B | ch } )

  proof
    wph
    wps
    vx
    cA
    crab
    wch
    vx
    cA
    crab
    wch
    vx
    cB
    crab
    wph
    wps
    wch
    vx
    cA
    bj-rabeqbida.nf
    bj-rabeqbida.2
    bj-rabbida
    wph
    wch
    vx
    cA
    cB
    bj-rabeqbida.nf
    bj-rabeqbida.1
    bj-rabeqd
    eqtrd
end
