include "wi.mm"
include "wrex.mm"
include "rexim.mm"
include "mprg.mm"

theorem reximia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume reximia.1: |- ( x e. A -> ( ph -> ps ) )


  assert |- ( E. x e. A ph -> E. x e. A ps )

  proof
    wph
    wps
    wi
    wph
    vx
    cA
    wrex
    wps
    vx
    cA
    wrex
    wi
    vx
    cA
    wph
    wps
    vx
    cA
    rexim
    reximia.1
    mprg
end
