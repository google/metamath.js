include "clo.mm"
include "ccop.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wreu.mm"
include "wrex.mm"
include "cnlnadjeu.mm"
include "reurex.mm"
include "syl.mm"

theorem cnlnadj
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cT: class T

  disjoint t x
  disjoint t y
  disjoint T t
  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( T e. ( LinOp i^i ContOp ) -> E. t e. ( LinOp i^i ContOp ) A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( t ` y ) ) )

  proof
    cT
    clo
    ccop
    cin
    #
    wcel
    vx
    cv
    #
    cT
    cfv
    vy
    cv
    #
    csp
    co
    @1
    @2
    vt
    cv
    cfv
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vt
    @0
    wreu
    @3
    vt
    @0
    wrex
    vx
    vy
    vt
    cT
    cnlnadjeu
    @3
    vt
    @0
    reurex
    syl
end
