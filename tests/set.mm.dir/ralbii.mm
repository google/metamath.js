include "cv.mm"
include "wcel.mm"
include "imbi2i.mm"
include "ralbii2.mm"

theorem ralbii
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  assume ralbii.1: |- ( ph <-> ps )


  assert |- ( A. x e. A ph <-> A. x e. A ps )

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
    ralbii.1
    imbi2i
    ralbii2
end
