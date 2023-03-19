include "wral.mm"
include "wsb.mm"
include "wcel.mm"
include "wsbc.mm"
include "cbvralsv.mm"
include "dfsbcq2.mm"
include "rspcv.mm"
include "syl5bi.mm"

theorem rspsbc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  assert |- ( A e. B -> ( A. x e. B ph -> [. A / x ]. ph ) )

  proof
    wph
    vx
    cB
    wral
    wph
    vx
    vy
    wsb
    #
    vy
    cB
    wral
    cA
    cB
    wcel
    wph
    vx
    cA
    wsbc
    #
    wph
    vx
    vy
    cB
    cbvralsv
    @0
    @1
    vy
    cA
    cB
    wph
    vx
    vy
    cA
    dfsbcq2
    rspcv
    syl5bi
end
