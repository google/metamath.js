include "wi.mm"
include "id.mm"
include "ral2imi.mm"

theorem ralim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph -> ps ) -> ( A. x e. A ph -> A. x e. A ps ) )

  proof
    wph
    wps
    wi
    #
    wph
    wps
    vx
    cA
    @0
    id
    ral2imi
end
