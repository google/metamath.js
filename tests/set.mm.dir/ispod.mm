include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "3ad2antr1.mm"
include "jca.mm"
include "ralrimivvva.mm"
include "df-po.mm"
include "sylibr.mm"

theorem ispod
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cR: class R
  assume ispod.1: |- ( ( ph /\ x e. A ) -> -. x R x )
  assume ispod.2: |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x R y /\ y R z ) -> x R z ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> R Po A )

  proof
    wph
    vx
    cv
    #
    @0
    cR
    wbr
    wn
    #
    @0
    vy
    cv
    #
    cR
    wbr
    @2
    vz
    cv
    #
    cR
    wbr
    wa
    @0
    @3
    cR
    wbr
    wi
    #
    wa
    #
    vz
    cA
    wral
    vy
    cA
    wral
    vx
    cA
    wral
    cA
    cR
    wpo
    wph
    @5
    vx
    vy
    vz
    cA
    cA
    cA
    wph
    @0
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    w3a
    wa
    @1
    @4
    wph
    @7
    @6
    @1
    @8
    ispod.1
    3ad2antr1
    ispod.2
    jca
    ralrimivvva
    vx
    vy
    vz
    cA
    cR
    df-po
    sylibr
end
