include "crab.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "df-rab.mm"
include "ssab2.mm"
include "eqsstri.mm"

theorem ssrab2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- { x e. A | ph } C_ A

  proof
    wph
    vx
    cA
    crab
    vx
    cv
    cA
    wcel
    wph
    wa
    vx
    cab
    cA
    wph
    vx
    cA
    df-rab
    wph
    vx
    cA
    ssab2
    eqsstri
end
