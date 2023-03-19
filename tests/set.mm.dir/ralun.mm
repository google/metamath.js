include "cun.mm"
include "wral.mm"
include "wa.mm"
include "ralunb.mm"
include "biimpri.mm"

theorem ralun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( ( A. x e. A ph /\ A. x e. B ph ) -> A. x e. ( A u. B ) ph )

  proof
    wph
    vx
    cA
    cB
    cun
    wral
    wph
    vx
    cA
    wral
    wph
    vx
    cB
    wral
    wa
    wph
    vx
    cA
    cB
    ralunb
    biimpri
end
