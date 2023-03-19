include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "idinxpssinxp.mm"
include "idinxpssinxp2.mm"
include "bitr3i.mm"

theorem idinxpssinxp4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( A. x e. A A. y e. A ( x = y -> x R y ) <-> A. x e. A x R x )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    @0
    @1
    cR
    wbr
    wi
    vy
    cA
    wral
    vx
    cA
    wral
    cid
    cA
    cA
    cxp
    #
    cin
    cR
    @2
    cin
    wss
    @0
    @0
    cR
    wbr
    vx
    cA
    wral
    vx
    vy
    cA
    cA
    cR
    idinxpssinxp
    vx
    cA
    cR
    idinxpssinxp2
    bitr3i
end
