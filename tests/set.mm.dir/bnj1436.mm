include "cv.mm"
include "wcel.mm"
include "abeq2i.mm"
include "biimpi.mm"

theorem bnj1436
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume bnj1436.1: |- A = { x | ph }


  assert |- ( x e. A -> ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    wph
    vx
    cA
    bnj1436.1
    abeq2i
    biimpi
end
