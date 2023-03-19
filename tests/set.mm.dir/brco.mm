include "cvv.mm"
include "wcel.mm"
include "ccom.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "brcog.mm"
include "mp2an.mm"

theorem brco
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelco.1: |- A e. _V
  assume opelco.2: |- B e. _V

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  assert |- ( A ( C o. D ) B <-> E. x ( A D x /\ x C B ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cC
    cD
    ccom
    wbr
    cA
    vx
    cv
    #
    cD
    wbr
    @0
    cB
    cC
    wbr
    wa
    vx
    wex
    wb
    opelco.1
    opelco.2
    vx
    cA
    cB
    cC
    cD
    cvv
    cvv
    brcog
    mp2an
end
