include "clb.mm"
include "wbr.mm"
include "ccnv.mm"
include "cub.mm"
include "cv.mm"
include "wral.mm"
include "df-lb.mm"
include "breqi.mm"
include "brub.mm"
include "vex.mm"
include "brcnv.mm"
include "ralbii.mm"
include "3bitri.mm"

theorem brlb
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cS: class S
  assume brub.1: |- S e. _V
  assume brub.2: |- A e. _V

  disjoint A x
  disjoint R x
  disjoint S x
  assert |- ( S LB R A <-> A. x e. S A R x )

  proof
    cS
    cA
    cR
    clb
    #
    wbr
    cS
    cA
    cR
    ccnv
    #
    cub
    #
    wbr
    vx
    cv
    #
    cA
    @1
    wbr
    #
    vx
    cS
    wral
    cA
    @3
    cR
    wbr
    #
    vx
    cS
    wral
    cS
    cA
    @0
    @2
    cR
    df-lb
    breqi
    vx
    cA
    @1
    cS
    brub.1
    brub.2
    brub
    @4
    @5
    vx
    cS
    @3
    cA
    cR
    vx
    vex
    brub.2
    brcnv
    ralbii
    3bitri
end
