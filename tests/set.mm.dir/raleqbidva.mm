include "wral.mm"
include "ralbidva.mm"
include "raleqdv.mm"
include "bitrd.mm"

theorem raleqbidva
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
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    wral
    wch
    vx
    cA
    wral
    wch
    vx
    cB
    wral
    wph
    wps
    wch
    vx
    cA
    raleqbidva.2
    ralbidva
    wph
    wch
    vx
    cA
    cB
    raleqbidva.1
    raleqdv
    bitrd
end
