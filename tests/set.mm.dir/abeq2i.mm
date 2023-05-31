include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wtru.mm"
include "cab.mm"
include "wceq.mm"
include "a1i.mm"
include "abeq2d.mm"
include "trud.mm"

theorem abeq2i
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  assume abeq2i.1: |- A = { x | ph }


  assert |- ( x e. A <-> ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    wb
    wtru
    wph
    vx
    cA
    cA
    wph
    vx
    cab
    wceq
    wtru
    abeq2i.1
    a1i
    abeq2d
    trud
end
