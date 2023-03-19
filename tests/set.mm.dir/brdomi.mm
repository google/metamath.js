include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "brdomg.mm"
include "syl.mm"
include "ibi.mm"

theorem brdomi
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cC: class C

  disjoint A f
  disjoint B f
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  assert |- ( A ~<_ B -> E. f f : A -1-1-> B )

  proof
    cA
    cB
    cdom
    wbr
    #
    cA
    cB
    vf
    cv
    wf1
    vf
    wex
    #
    @0
    cB
    cvv
    wcel
    @0
    @1
    wb
    cA
    cB
    cdom
    reldom
    brrelex2i
    cA
    cB
    cvv
    vf
    brdomg
    syl
    ibi
end
