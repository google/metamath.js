include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wrmo.mm"
include "wreu.mm"
include "infmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem infeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  assume infmo.1: |- ( ph -> R Or A )
  assume infeu.2: |- ( ph -> E. x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint ph w
  assert |- ( ph -> E! x e. A ( A. y e. B -. y R x /\ A. y e. A ( x R y -> E. z e. B z R y ) ) )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    wn
    vy
    cB
    wral
    @1
    @0
    cR
    wbr
    vz
    cv
    @0
    cR
    wbr
    vz
    cB
    wrex
    wi
    vy
    cA
    wral
    wa
    #
    vx
    cA
    wrex
    @2
    vx
    cA
    wrmo
    @2
    vx
    cA
    wreu
    infeu.2
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    infmo.1
    infmo
    @2
    vx
    cA
    reu5
    sylanbrc
end
