include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wrmo.mm"
include "wreu.mm"
include "supmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem supeu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let vw: setvar w
  let cC: class C
  assume supmo.1: |- ( ph -> R Or A )
  assume supeu.2: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

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
  disjoint C w
  disjoint ph w
  assert |- ( ph -> E! x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

  proof
    wph
    vx
    cv
    #
    vy
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
    @1
    vz
    cv
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
    supeu.2
    wph
    vx
    vy
    vz
    cA
    cB
    cR
    supmo.1
    supmo
    @2
    vx
    cA
    reu5
    sylanbrc
end
