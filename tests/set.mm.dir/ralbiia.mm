include "cv.mm"
include "wcel.mm"
include "pm5.74i.mm"
include "ralbii2.mm"

theorem ralbiia
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ralbiia.1: |- ( x e. A -> ( ph <-> ps ) )


  assert |- ( A. x e. A ph <-> A. x e. A ps )

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
    ralbiia.1
    pm5.74i
    ralbii2
end
