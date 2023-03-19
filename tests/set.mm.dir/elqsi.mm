include "cqs.mm"
include "wcel.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "elqsg.mm"
include "ibi.mm"

theorem elqsi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R

  disjoint A x
  disjoint B x
  disjoint R x
  assert |- ( B e. ( A /. R ) -> E. x e. A B = [ x ] R )

  proof
    cB
    cA
    cR
    cqs
    #
    wcel
    cB
    vx
    cv
    cR
    cec
    wceq
    vx
    cA
    wrex
    vx
    cA
    cB
    cR
    @0
    elqsg
    ibi
end
