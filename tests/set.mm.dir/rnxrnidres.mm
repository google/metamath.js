include "cid.mm"
include "cres.mm"
include "cxrn.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "wceq.mm"
include "rnxrnres.mm"
include "wb.mm"
include "cvv.mm"
include "ideqg.mm"
include "elv.mm"
include "anbi1ci.mm"
include "rexbii.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem rnxrnidres
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let cR: class R

  disjoint A u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint R u
  disjoint R x
  disjoint R y
  assert |- ran ( R |X. ( _I |` A ) ) = { <. x , y >. | E. u e. A ( u = y /\ u R x ) }

  proof
    cR
    cid
    cA
    cres
    cxrn
    crn
    vu
    cv
    #
    vx
    cv
    cR
    wbr
    #
    @0
    vy
    cv
    #
    cid
    wbr
    #
    wa
    #
    vu
    cA
    wrex
    #
    vx
    vy
    copab
    @0
    @2
    wceq
    #
    @1
    wa
    #
    vu
    cA
    wrex
    #
    vx
    vy
    copab
    vx
    vy
    vu
    cA
    cR
    cid
    rnxrnres
    @5
    @8
    vx
    vy
    @4
    @7
    vu
    cA
    @3
    @6
    @1
    @3
    @6
    wb
    vy
    @0
    @2
    cvv
    ideqg
    elv
    anbi1ci
    rexbii
    opabbii
    eqtri
end
