include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "abssi.mm"

theorem ssab2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- { x | ( x e. A /\ ph ) } C_ A

  proof
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    cA
    @0
    wph
    simpl
    abssi
end
