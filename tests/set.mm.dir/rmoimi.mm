include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "rmoimia.mm"

theorem rmoimi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume rmoimi.1: |- ( ph -> ps )


  assert |- ( E* x e. A ps -> E* x e. A ph )

  proof
    wph
    wps
    vx
    cA
    wph
    wps
    wi
    vx
    cv
    cA
    wcel
    rmoimi.1
    a1i
    rmoimia
end
