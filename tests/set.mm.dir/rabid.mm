include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "df-rab.mm"
include "abeq2i.mm"

theorem rabid
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( x e. { x e. A | ph } <-> ( x e. A /\ ph ) )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    vx
    wph
    vx
    cA
    crab
    wph
    vx
    cA
    df-rab
    abeq2i
end
