include "wrex.mm"
include "rexeqdv.mm"
include "rexbidv.mm"
include "bitrd.mm"

theorem rexeqbidv
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
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) )

  proof
    wph
    wps
    vx
    cA
    wrex
    wps
    vx
    cB
    wrex
    wch
    vx
    cB
    wrex
    wph
    wps
    vx
    cA
    cB
    raleqbidv.1
    rexeqdv
    wph
    wps
    wch
    vx
    cB
    raleqbidv.2
    rexbidv
    bitrd
end
