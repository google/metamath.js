include "cvv.mm"
include "cxp.mm"
include "cimage.mm"
include "cep.mm"
include "ccnv.mm"
include "ccom.mm"
include "cima.mm"
include "df-image.mm"
include "wbr.mm"
include "wcel.mm"
include "brxp.mm"
include "mpbir2an.mm"
include "cv.mm"
include "wrex.mm"
include "vex.mm"
include "brcnv.mm"
include "rexbii.mm"
include "coep.mm"
include "elima.mm"
include "3bitr4ri.mm"
include "brtxpsd3.mm"

theorem brimage
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume brimage.1: |- A e. _V
  assume brimage.2: |- B e. _V


  assert |- ( A Image R B <-> B = ( R " A ) )

  proof
    vx
    cA
    cB
    cvv
    cvv
    cxp
    #
    cR
    cimage
    cep
    cR
    ccnv
    #
    ccom
    #
    cR
    cA
    cima
    #
    brimage.1
    brimage.2
    cR
    df-image
    cA
    cB
    @0
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    brimage.1
    brimage.2
    cA
    cB
    cvv
    cvv
    brxp
    mpbir2an
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    #
    vy
    cA
    wrex
    @5
    @4
    cR
    wbr
    #
    vy
    cA
    wrex
    @4
    cA
    @2
    wbr
    @4
    @3
    wcel
    @6
    @7
    vy
    cA
    @4
    @5
    cR
    vx
    vex
    #
    vy
    vex
    brcnv
    rexbii
    vy
    @4
    cA
    @1
    @8
    brimage.1
    coep
    vy
    @4
    cR
    cA
    @8
    elima
    3bitr4ri
    brtxpsd3
end
