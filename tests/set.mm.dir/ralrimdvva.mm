include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ex.mm"
include "com23.mm"
include "ralrimdvv.mm"

theorem ralrimdvva
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralrimdvva.1: |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) )

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
    vx
    vy
    cA
    cB
    wph
    vx
    cv
    cA
    wcel
    vy
    cv
    cB
    wcel
    wa
    #
    wps
    wch
    wph
    @0
    wps
    wch
    wi
    ralrimdvva.1
    ex
    com23
    ralrimdvv
end
