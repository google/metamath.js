include "crab.mm"
include "rabbidva.mm"
include "rabeqdv.mm"
include "eqtrd.mm"

theorem rabeqbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabeqbidva.1: |- ( ph -> A = B )
  assume rabeqbidva.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

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
    rabeqbidva.2
    rabbidva
    wph
    wch
    vx
    cA
    cB
    rabeqbidva.1
    rabeqdv
    eqtrd
end
