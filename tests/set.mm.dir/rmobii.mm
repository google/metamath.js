include "wb.mm"
include "cv.mm"
include "wcel.mm"
include "a1i.mm"
include "rmobiia.mm"

theorem rmobii
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume rmobii.1: |- ( ph <-> ps )


  assert |- ( E* x e. A ph <-> E* x e. A ps )

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
    rmobii.1
    a1i
    rmobiia
end
