include "wor.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "supub.mm"

theorem supubt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( R Or A /\ E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) ) -> ( C e. B -> -. sup ( B , A , R ) R C ) )

  proof
    cA
    cR
    wor
    #
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
    @2
    @1
    cR
    wbr
    @2
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
    vx
    cA
    wrex
    #
    wa
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    @0
    @3
    simpl
    @0
    @3
    simpr
    supub
end
