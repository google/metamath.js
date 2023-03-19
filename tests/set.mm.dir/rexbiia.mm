include "cv.mm"
include "wcel.mm"
include "pm5.32i.mm"
include "rexbii2.mm"

theorem rexbiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rexbiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- ( E. x e. A ph <-> E. x e. A ps )

  proof
    wph
    wps
    vx
    cA
    cA
    vx
    cv
    cA
    wcel
    wph
    wps
    rexbiia.1
    pm5.32i
    rexbii2
end
