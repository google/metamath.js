include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "abeq2.mm"
include "mpgbir.mm"

theorem abbi2i
  param wph: wff ph
  param vx: setvar x
  param cA: class A
  assume abbi2i.1: |- ( x e. A <-> ph )

  disjoint A x
  assert |- A = { x | ph }

  proof
    cA
    wph
    vx
    cab
    wceq
    vx
    cv
    cA
    wcel
    wph
    wb
    vx
    wph
    vx
    cA
    abeq2
    abbi2i.1
    mpgbir
end
