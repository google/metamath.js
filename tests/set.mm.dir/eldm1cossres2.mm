include "wcel.mm"
include "cres.mm"
include "ccoss.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "cec.mm"
include "eldm1cossres.mm"
include "wb.mm"
include "cvv.mm"
include "elecALTV.mm"
include "el2v1.mm"
include "rexbidv.mm"
include "bitr4d.mm"

theorem eldm1cossres2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint R x
  disjoint V x
  assert |- ( B e. V -> ( B e. dom ,~ ( R |` A ) <-> E. x e. A B e. [ x ] R ) )

  proof
    cB
    cV
    wcel
    #
    cB
    cR
    cA
    cres
    ccoss
    cdm
    wcel
    vx
    cv
    #
    cB
    cR
    wbr
    #
    vx
    cA
    wrex
    cB
    @1
    cR
    cec
    wcel
    #
    vx
    cA
    wrex
    vx
    cA
    cB
    cR
    cV
    eldm1cossres
    @0
    @3
    @2
    vx
    cA
    @0
    @3
    @2
    wb
    vx
    @1
    cB
    cR
    cvv
    cV
    elecALTV
    el2v1
    rexbidv
    bitr4d
end
