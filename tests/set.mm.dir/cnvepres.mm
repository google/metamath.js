include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "dfres2.mm"
include "wb.mm"
include "cvv.mm"
include "brcnvep.mm"
include "elv.mm"
include "anbi2i.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem cnvepres
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( `' _E |` A ) = { <. x , y >. | ( x e. A /\ y e. x ) }

  proof
    cep
    ccnv
    #
    cA
    cres
    vx
    cv
    #
    cA
    wcel
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
    vx
    vy
    copab
    @2
    @3
    @1
    wcel
    #
    wa
    #
    vx
    vy
    copab
    vx
    vy
    cA
    @0
    dfres2
    @5
    @7
    vx
    vy
    @4
    @6
    @2
    @4
    @6
    wb
    vx
    @1
    @3
    cvv
    brcnvep
    elv
    anbi2i
    opabbii
    eqtri
end
