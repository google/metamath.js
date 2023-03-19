include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wa.mm"
include "cen.mm"
include "wn.mm"
include "sdomdom.mm"
include "domtr.mm"
include "sylan2.mm"
include "simpr.mm"
include "ensym.mm"
include "simpl.mm"
include "endomtr.mm"
include "syl2anr.mm"
include "domnsym.mm"
include "syl.mm"
include "ex.mm"
include "mt2d.mm"
include "brsdom.mm"
include "sylanbrc.mm"

theorem domsdomtr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A ~<_ B /\ B ~< C ) -> A ~< C )

  proof
    cA
    cB
    cdom
    wbr
    #
    cB
    cC
    csdm
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
    @1
    @0
    cB
    cC
    cdom
    wbr
    @3
    cB
    cC
    sdomdom
    cA
    cB
    cC
    domtr
    sylan2
    @2
    @4
    @1
    @0
    @1
    simpr
    @2
    @4
    @1
    wn
    #
    @2
    @4
    wa
    cC
    cB
    cdom
    wbr
    #
    @5
    @4
    cC
    cA
    cen
    wbr
    @0
    @6
    @2
    cA
    cC
    ensym
    @0
    @1
    simpl
    cC
    cA
    cB
    endomtr
    syl2anr
    cC
    cB
    domnsym
    syl
    ex
    mt2d
    cA
    cC
    brsdom
    sylanbrc
end
