include "cv.mm"
include "wcel.mm"
include "bnj1196.mm"
include "bnj1266.mm"
include "bnj937.mm"

theorem bnj1265
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1265.1: |- ( ph -> E. x e. A ps )

  disjoint ps x
  assert |- ( ph -> ps )

  proof
    wph
    wps
    vx
    vx
    cv
    cA
    wcel
    wps
    wph
    vx
    wph
    wps
    vx
    cA
    bnj1265.1
    bnj1196
    bnj1266
    bnj937
end
