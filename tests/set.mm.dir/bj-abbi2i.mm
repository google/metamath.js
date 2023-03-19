include "cab.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "bj-abeq2.mm"
include "mpgbir.mm"

theorem bj-abbi2i
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume bj-abbi2i.1: |- ( x e. A <-> ph )

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
    bj-abeq2
    bj-abbi2i.1
    mpgbir
end
