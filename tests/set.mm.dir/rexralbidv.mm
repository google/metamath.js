include "wral.mm"
include "ralbidv.mm"
include "rexbidv.mm"

theorem rexralbidv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume 2rexbidv.1: |- ( ph -> ( ps <-> ch ) )

  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( E. x e. A A. y e. B ps <-> E. x e. A A. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wral
    wch
    vy
    cB
    wral
    vx
    cA
    wph
    wps
    wch
    vy
    cB
    2rexbidv.1
    ralbidv
    rexbidv
end
