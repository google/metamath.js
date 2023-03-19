include "wral.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem raleqbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqbidv.1: |- ( ph -> A = B )
  assume raleqbidv.2: |- ( ph -> ( ps <-> ch ) )

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
    wps
    vx
    cB
    wral
    wch
    vx
    cB
    wral
    wph
    wps
    vx
    cA
    cB
    raleqbidv.1
    raleqdv
    wph
    wps
    wch
    vx
    cB
    raleqbidv.2
    ralbidv
    bitrd
end
