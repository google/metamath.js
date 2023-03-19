include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "csup.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "expr.mm"
include "eqsup.mm"
include "mp3and.mm"

theorem eqsupd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vw: setvar w
  assume supmo.1: |- ( ph -> R Or A )
  assume eqsupd.2: |- ( ph -> C e. A )
  assume eqsupd.3: |- ( ( ph /\ y e. B ) -> -. C R y )
  assume eqsupd.4: |- ( ( ph /\ ( y e. A /\ y R C ) ) -> E. z e. B y R z )

  disjoint C y
  disjoint ph y
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint R y
  disjoint R z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint C x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint R x
  disjoint R w
  disjoint B x
  disjoint B w
  disjoint C w
  disjoint ph w
  assert |- ( ph -> sup ( B , A , R ) = C )

  proof
    wph
    cC
    cA
    wcel
    cC
    vy
    cv
    #
    cR
    wbr
    wn
    #
    vy
    cB
    wral
    @0
    cC
    cR
    wbr
    #
    @0
    vz
    cv
    cR
    wbr
    vz
    cB
    wrex
    #
    wi
    #
    vy
    cA
    wral
    cB
    cA
    cR
    csup
    cC
    wceq
    eqsupd.2
    wph
    @1
    vy
    cB
    eqsupd.3
    ralrimiva
    wph
    @4
    vy
    cA
    wph
    @0
    cA
    wcel
    @2
    @3
    eqsupd.4
    expr
    ralrimiva
    wph
    vy
    vz
    cA
    cB
    cC
    cR
    supmo.1
    eqsup
    mp3and
end
