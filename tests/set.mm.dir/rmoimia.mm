include "wi.mm"
include "wrmo.mm"
include "rmoim.mm"
include "mprg.mm"

theorem rmoimia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rmoimia.1: |- ( x e. A -> ( ph -> ps ) )


  assert |- ( E* x e. A ps -> E* x e. A ph )

  proof
    wph
    wps
    wi
    wps
    vx
    cA
    wrmo
    wph
    vx
    cA
    wrmo
    wi
    vx
    cA
    wph
    wps
    vx
    cA
    rmoim
    rmoimia.1
    mprg
end
