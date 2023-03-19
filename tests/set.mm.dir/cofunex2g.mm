include "ccnv.mm"
include "wfun.mm"
include "wcel.mm"
include "ccom.mm"
include "cvv.mm"
include "wa.mm"
include "cnvexg.mm"
include "cofunexg.mm"
include "sylan2.mm"
include "cnvco.mm"
include "cocnvcnv2.mm"
include "cocnvcnv1.mm"
include "3eqtrri.mm"
include "syl5eqel.mm"
include "syl.mm"
include "ancoms.mm"

theorem cofunex2g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ Fun `' B ) -> ( A o. B ) e. _V )

  proof
    cB
    ccnv
    #
    wfun
    #
    cA
    cV
    wcel
    #
    cA
    cB
    ccom
    #
    cvv
    wcel
    #
    @1
    @2
    wa
    @0
    cA
    ccnv
    #
    ccom
    #
    cvv
    wcel
    #
    @4
    @2
    @1
    @5
    cvv
    wcel
    @7
    cA
    cV
    cnvexg
    @0
    @5
    cvv
    cofunexg
    sylan2
    @7
    @3
    @6
    ccnv
    #
    cvv
    @8
    @5
    ccnv
    #
    @0
    ccnv
    ccom
    @9
    cB
    ccom
    @3
    @0
    @5
    cnvco
    @9
    cB
    cocnvcnv2
    cA
    cB
    cocnvcnv1
    3eqtrri
    @6
    cvv
    cnvexg
    syl5eqel
    syl
    ancoms
end
