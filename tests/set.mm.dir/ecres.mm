include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "cres.mm"
include "cec.mm"
include "wb.mm"
include "cvv.mm"
include "elecres.mm"
include "elv.mm"
include "abbi2i.mm"

theorem ecres
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- [ B ] ( R |` A ) = { x | ( B e. A /\ B R x ) }

  proof
    cB
    cA
    wcel
    cB
    vx
    cv
    #
    cR
    wbr
    wa
    #
    vx
    cB
    cR
    cA
    cres
    cec
    #
    @0
    @2
    wcel
    @1
    wb
    vx
    cA
    cB
    @0
    cR
    cvv
    elecres
    elv
    abbi2i
end
