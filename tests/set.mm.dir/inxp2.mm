include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "wceq.mm"
include "relinxp.mm"
include "dfrel4v.mm"
include "mpbi.mm"
include "brinxp2ALTV.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem inxp2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  assert |- ( R i^i ( A X. B ) ) = { <. x , y >. | ( ( x e. A /\ y e. B ) /\ x R y ) }

  proof
    cR
    cA
    cB
    cxp
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vx
    vy
    copab
    #
    @1
    cA
    wcel
    @2
    cB
    wcel
    wa
    @1
    @2
    cR
    wbr
    wa
    #
    vx
    vy
    copab
    @0
    wrel
    @0
    @4
    wceq
    cA
    cB
    cR
    relinxp
    vx
    vy
    @0
    dfrel4v
    mpbi
    @3
    @5
    vx
    vy
    cA
    cB
    @1
    @2
    cR
    brinxp2ALTV
    opabbii
    eqtri
end
