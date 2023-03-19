include "wral.mm"
include "nfra1.mm"
include "nf5ri.mm"

theorem hbra1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ph -> A. x A. x e. A ph )

  proof
    wph
    vx
    cA
    wral
    vx
    wph
    vx
    cA
    nfra1
    nf5ri
end
