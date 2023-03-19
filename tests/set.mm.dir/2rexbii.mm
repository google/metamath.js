include "wrex.mm"
include "rexbii.mm"

theorem 2rexbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume rexbii.1: |- ( ph <-> ps )


  assert |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps )

  proof
    wph
    vy
    cB
    wrex
    wps
    vy
    cB
    wrex
    vx
    cA
    wph
    wps
    vy
    cB
    rexbii.1
    rexbii
    rexbii
end
