include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wa.mm"
include "cen.mm"
include "wn.mm"
include "sdomdom.mm"
include "domtr.mm"
include "sylan.mm"
include "simpl.mm"
include "simpr.mm"
include "ensym.mm"
include "domentr.mm"
include "syl2an.mm"
include "domnsym.mm"
include "syl.mm"
include "ex.mm"
include "mt2d.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem sdomdomtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~< B /\ B ~<_ C ) -> A ~< C )

  proof
    cA
    cB
    csdm
    wbr
    #
    cB
    cC
    cdom
    wbr
    #
    wa
    #
    cA
    cC
    cdom
    wbr
    #
    cA
    cC
    cen
    wbr
    #
    wn
    cA
    cC
    csdm
    wbr
    @0
    cA
    cB
    cdom
    wbr
    @1
    @3
    cA
    cB
    sdomdom
    cA
    cB
    cC
    domtr
    sylan
    @2
    @4
    @0
    @0
    @1
    simpl
    @2
    @4
    @0
    wn
    #
    @2
    @4
    wa
    cB
    cA
    cdom
    wbr
    #
    @5
    @2
    @1
    cC
    cA
    cen
    wbr
    @6
    @4
    @0
    @1
    simpr
    cA
    cC
    ensym
    cB
    cC
    cA
    domentr
    syl2an
    cB
    cA
    domnsym
    syl
    ex
    mt2d
    cA
    cC
    brsdom
    sylanbrc
end
