include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "ssab2.mm"
include "ssexi.mm"

theorem zfausab
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume zfausab.1: |- A e. _V

  disjoint A x
  assert |- { x | ( x e. A /\ ph ) } e. _V

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    vx
    cab
    cA
    zfausab.1
    wph
    vx
    cA
    ssab2
    ssexi
end
