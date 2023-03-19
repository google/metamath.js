include "ccoels.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "ccoss.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wrex.mm"
include "copab.mm"
include "wcel.mm"
include "df-coels.mm"
include "1cossres.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvep.mm"
include "elv.mm"
include "anbi12i.mm"
include "rexbii.mm"
include "opabbii.mm"
include "3eqtri.mm"

theorem dfcoels
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A

  disjoint A u
  disjoint A x
  disjoint A y
  disjoint u x
  disjoint u y
  disjoint x y
  assert |- ~ A = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  proof
    cA
    ccoels
    cep
    ccnv
    #
    cA
    cres
    ccoss
    vu
    cv
    #
    vx
    cv
    #
    @0
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
    @2
    @1
    wcel
    #
    @4
    @1
    wcel
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
    cA
    df-coels
    vx
    vy
    vu
    cA
    @0
    1cossres
    @7
    @11
    vx
    vy
    @6
    @10
    vu
    cA
    @3
    @8
    @5
    @9
    @3
    @8
    wb
    vu
    @1
    @2
    cvv
    brcnvep
    elv
    @5
    @9
    wb
    vu
    @1
    @4
    cvv
    brcnvep
    elv
    anbi12i
    rexbii
    opabbii
    3eqtri
end
