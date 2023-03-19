include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wor.mm"
include "ralrimivva.mm"
include "df-so.mm"
include "sylanbrc.mm"

theorem issod
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  assume issod.1: |- ( ph -> R Po A )
  assume issod.2: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x R y \/ x = y \/ y R x ) )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> R Or A )

  proof
    wph
    cA
    cR
    wpo
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    vx
    vy
    weq
    @1
    @0
    cR
    wbr
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cR
    wor
    issod.1
    wph
    @2
    vx
    vy
    cA
    cA
    issod.2
    ralrimivva
    vx
    vy
    cA
    cR
    df-so
    sylanbrc
end
