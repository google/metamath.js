include "crab.mm"
include "rabeqdv.mm"
include "rabbidv.mm"
include "eqtrd.mm"

theorem rabeqbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqbidv.1: |- ( ph -> A = B )
  assume rabeqbidv.2: |- ( ph -> ( ps <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ph x
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
    rabeqbidv.1
    rabeqdv
    wph
    wps
    wch
    vx
    cB
    rabeqbidv.2
    rabbidv
    eqtrd
end
