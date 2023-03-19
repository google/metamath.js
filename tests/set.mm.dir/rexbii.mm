include "cv.mm"
include "wcel.mm"
include "anbi2i.mm"
include "rexbii2.mm"

theorem rexbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rexbii.1: |- ( ph <-> ps )


  assert |- ( E. x e. A ph <-> E. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    cA
    wph
    wps
    vx
    cv
    cA
    wcel
    rexbii.1
    anbi2i
    rexbii2
end
