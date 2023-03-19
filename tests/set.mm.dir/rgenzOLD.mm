include "wral.mm"
include "c0.mm"
include "rzal.mm"
include "wne.mm"
include "ralrimiva.mm"
include "pm2.61ine.mm"

theorem rgenzOLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume rgenzOLD.1: |- ( ( A =/= (/) /\ x e. A ) -> ph )

  disjoint A x
  assert |- A. x e. A ph

  proof
    wph
    vx
    cA
    wral
    cA
    c0
    wph
    vx
    cA
    rzal
    cA
    c0
    wne
    wph
    vx
    cA
    rgenzOLD.1
    ralrimiva
    pm2.61ine
end
