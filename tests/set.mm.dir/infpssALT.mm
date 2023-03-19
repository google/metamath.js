include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wpss.mm"
include "cen.mm"
include "wa.mm"
include "wex.mm"
include "cfin4.mm"
include "wcel.mm"
include "ominf4.mm"
include "wn.mm"
include "cvv.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "isfin4.mm"
include "syl.mm"
include "domfin4.mm"
include "expcom.mm"
include "sylbird.mm"
include "mt3i.mm"

theorem infpssALT
  let vx: setvar x
  let cA: class A
  let vc: setvar c
  let vf: setvar f
  let cB: class B

  disjoint A x
  disjoint c f
  disjoint c x
  disjoint A c
  disjoint f x
  disjoint A f
  disjoint B c
  disjoint B f
  disjoint B x
  assert |- ( _om ~<_ A -> E. x ( x C. A /\ x ~~ A ) )

  proof
    com
    cA
    cdom
    wbr
    #
    vx
    cv
    #
    cA
    wpss
    @1
    cA
    cen
    wbr
    wa
    vx
    wex
    #
    com
    cfin4
    wcel
    #
    ominf4
    @0
    @2
    wn
    #
    cA
    cfin4
    wcel
    #
    @3
    @0
    cA
    cvv
    wcel
    @5
    @4
    wb
    com
    cA
    cdom
    reldom
    brrelex2i
    vx
    cA
    cvv
    isfin4
    syl
    @5
    @0
    @3
    cA
    com
    domfin4
    expcom
    sylbird
    mt3i
end
