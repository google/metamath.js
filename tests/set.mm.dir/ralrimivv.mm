include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "expd.mm"
include "ralrimdv.mm"
include "ralrimiv.mm"

theorem ralrimivv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume ralrimivv.1: |- ( ph -> ( ( x e. A /\ y e. B ) -> ps ) )

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A y
  assert |- ( ph -> A. x e. A A. y e. B ps )

  proof
    wph
    wps
    vy
    cB
    wral
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    #
    wps
    vy
    cB
    wph
    @0
    vy
    cv
    cB
    wcel
    wps
    ralrimivv.1
    expd
    ralrimdv
    ralrimiv
end
