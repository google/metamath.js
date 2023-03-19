include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "pm2.04.mm"
include "ralimi2.mm"
include "impbii.mm"

theorem ralcom3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A. x e. A ( x e. B -> ph ) <-> A. x e. B ( x e. A -> ph ) )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wi
    #
    vx
    cA
    wral
    @0
    cA
    wcel
    #
    wph
    wi
    #
    vx
    cB
    wral
    @2
    @4
    vx
    cA
    cB
    @3
    @1
    wph
    pm2.04
    ralimi2
    @4
    @2
    vx
    cB
    cA
    @1
    @3
    wph
    pm2.04
    ralimi2
    impbii
end
