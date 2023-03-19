include "wral.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "imp.mm"
include "ralrimivv.mm"
include "ex.mm"

theorem ralrimdvv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralrimdvv.1: |- ( ph -> ( ps -> ( ( x e. A /\ y e. B ) -> ch ) ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps y
  disjoint A y
  assert |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) )

  proof
    wph
    wps
    wch
    vy
    cB
    wral
    vx
    cA
    wral
    wph
    wps
    wa
    wch
    vx
    vy
    cA
    cB
    wph
    wps
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    wch
    wi
    ralrimdvv.1
    imp
    ralrimivv
    ex
end
