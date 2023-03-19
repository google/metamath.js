include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "csup.mm"
include "wa.mm"
include "wrex.mm"
include "suplub.mm"
include "expdimp.mm"
include "dfrex2.mm"
include "syl6ib.mm"
include "con2d.mm"
include "expimpd.mm"

theorem supnub
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vw: setvar w
  assume supmo.1: |- ( ph -> R Or A )
  assume supcl.2: |- ( ph -> E. x e. A ( A. y e. B -. x R y /\ A. y e. A ( y R x -> E. z e. B y R z ) ) )

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
  disjoint C z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R w
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> ( ( C e. A /\ A. z e. B -. C R z ) -> -. C R sup ( B , A , R ) ) )

  proof
    wph
    cC
    cA
    wcel
    #
    cC
    vz
    cv
    cR
    wbr
    #
    wn
    vz
    cB
    wral
    #
    cC
    cB
    cA
    cR
    csup
    cR
    wbr
    #
    wn
    wph
    @0
    wa
    #
    @3
    @2
    @4
    @3
    @1
    vz
    cB
    wrex
    #
    @2
    wn
    wph
    @0
    @3
    @5
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    supmo.1
    supcl.2
    suplub
    expdimp
    @1
    vz
    cB
    dfrex2
    syl6ib
    con2d
    expimpd
end
