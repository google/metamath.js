include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "reubiia.mm"

theorem reubii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume reubii.1: |- ( ph <-> ps )


  assert |- ( E! x e. A ph <-> E! x e. A ps )

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
    reubii.1
    a1i
    reubiia
end
