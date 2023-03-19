include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "reu5.mm"
include "simprbi.mm"

theorem reurmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E! x e. A ph -> E* x e. A ph )

  proof
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    wrex
    wph
    vx
    cA
    wrmo
    wph
    vx
    cA
    reu5
    simprbi
end
