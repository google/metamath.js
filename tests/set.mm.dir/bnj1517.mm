include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "bnj1436.mm"
include "simprd.mm"

theorem bnj1517
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bnj1517.1: |- A = { x | ( ph /\ ps ) }


  assert |- ( x e. A -> ps )

  proof
    vx
    cv
    cA
    wcel
    wph
    wps
    wph
    wps
    wa
    vx
    cA
    bnj1517.1
    bnj1436
    simprd
end
