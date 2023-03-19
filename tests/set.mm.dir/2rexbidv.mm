include "wrex.mm"
include "rexbidv.mm"

theorem 2rexbidv
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
  assert |- ( ph -> ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) )

  proof
    wph
    wps
    vy
    cB
    wrex
    wch
    vy
    cB
    wrex
    vx
    cA
    wph
    wps
    wch
    vy
    cB
    2rexbidv.1
    rexbidv
    rexbidv
end
