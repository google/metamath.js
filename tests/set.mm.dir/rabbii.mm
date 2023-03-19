include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "rabbiia.mm"

theorem rabbii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rabbii.1: |- ( ph <-> ps )


  assert |- { x e. A | ph } = { x e. A | ps }

  proof
    wph
    wps
    vx
    cA
    wph
    wps
    wb
    vx
    cv
    cA
    wcel
    rabbii.1
    a1i
    rabbiia
end
