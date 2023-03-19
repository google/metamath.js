include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "crab.mm"
include "cfn.mm"
include "ctopon.mm"
include "cfv.mm"
include "isfinite.mm"
include "orbi1i.mm"
include "rabbii.mm"
include "fctop.mm"
include "syl5eqelr.mm"

theorem fctop2
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. V -> { x e. ~P A | ( ( A \ x ) ~< _om \/ x = (/) ) } e. ( TopOn ` A ) )

  proof
    cA
    cV
    wcel
    cA
    vx
    cv
    #
    cdif
    #
    com
    csdm
    wbr
    #
    @0
    c0
    wceq
    #
    wo
    #
    vx
    cA
    cpw
    #
    crab
    @1
    cfn
    wcel
    #
    @3
    wo
    #
    vx
    @5
    crab
    cA
    ctopon
    cfv
    @7
    @4
    vx
    @5
    @6
    @2
    @3
    @1
    isfinite
    orbi1i
    rabbii
    vx
    cA
    cV
    fctop
    syl5eqelr
end
