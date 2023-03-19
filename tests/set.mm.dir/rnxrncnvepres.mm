include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cxrn.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "wcel.mm"
include "rnxrnres.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvep.mm"
include "elv.mm"
include "anbi1ci.mm"
include "rexbii.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem rnxrncnvepres
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
  assert |- ran ( R |X. ( `' _E |` A ) ) = { <. x , y >. | E. u e. A ( y e. u /\ u R x ) }

  proof
    cR
    cep
    ccnv
    #
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
    @1
    vy
    cv
    #
    @0
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
    @3
    @1
    wcel
    #
    @2
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
    @0
    rnxrnres
    @6
    @9
    vx
    vy
    @5
    @8
    vu
    cA
    @4
    @7
    @2
    @4
    @7
    wb
    vu
    @1
    @3
    cvv
    brcnvep
    elv
    anbi1ci
    rexbii
    opabbii
    eqtri
end
