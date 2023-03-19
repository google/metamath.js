include "wrex.mm"
include "rexbidva.mm"
include "rexeqdv.mm"
include "bitrd.mm"

theorem rexeqbidva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqbidva.1: |- ( ph -> A = B )
  assume raleqbidva.2: |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    wrex
    wch
    vx
    cA
    wrex
    wch
    vx
    cB
    wrex
    wph
    wps
    wch
    vx
    cA
    raleqbidva.2
    rexbidva
    wph
    wch
    vx
    cA
    cB
    raleqbidva.1
    rexeqdv
    bitrd
end
