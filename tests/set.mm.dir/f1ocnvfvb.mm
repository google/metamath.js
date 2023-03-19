include "wf1o.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "ccnv.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "3adant3.mm"
include "wa.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "f1ocnvfv2.mm"
include "eqeq2d.mm"
include "syl5ib.mm"
include "3adant2.mm"
include "impbid.mm"

theorem f1ocnvfvb
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A -1-1-onto-> B /\ C e. A /\ D e. B ) -> ( ( F ` C ) = D <-> ( `' F ` D ) = C ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    w3a
    cC
    cF
    cfv
    #
    cD
    wceq
    #
    cD
    cF
    ccnv
    cfv
    #
    cC
    wceq
    #
    @0
    @1
    @4
    @6
    wi
    @2
    cA
    cB
    cC
    cD
    cF
    f1ocnvfv
    3adant3
    @0
    @2
    @6
    @4
    wi
    @1
    @6
    @3
    @5
    cF
    cfv
    #
    wceq
    #
    @0
    @2
    wa
    #
    @4
    @8
    cC
    @5
    cC
    @5
    cF
    fveq2
    eqcoms
    @9
    @7
    cD
    @3
    cA
    cB
    cD
    cF
    f1ocnvfv2
    eqeq2d
    syl5ib
    3adant2
    impbid
end
