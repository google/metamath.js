include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "eqcomi.mm"
include "abeq2i.mm"
include "bicomi.mm"

theorem abeq1i
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume abeq1i.1: |- { x | ph } = A


  assert |- ( ph <-> x e. A )

  proof
    vx
    cv
    cA
    wcel
    wph
    wph
    vx
    cA
    wph
    vx
    cab
    cA
    abeq1i.1
    eqcomi
    abeq2i
    bicomi
end
